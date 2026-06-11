# Optimizing Lean 4 runtime performance: an emitted-C-driven workflow

Notes from optimizing this repo's verified fast implementation (Phases B–D in
[plan.md](plan.md)). The workflow took the AEAD from ~15 MB/s to ~344 MB/s
across three optimization phases and a follow-up `USize`-indexing pass, while
keeping every equivalence capstone's name, statement, and axiom set unchanged. The methodology should transfer to
any Lean 4 project with a hot path.

**A note on novelty**: the components are standard — inspecting generated code
is ordinary systems practice, the reuse/exclusivity model is documented in the
Lean compiler papers (Ullrich & de Moura, *Counting Immutable Beans*), and the
runtime header is public. What seems genuinely uncommon is the assembled
workflow for *application* authors: using the emitted C as a greppable
profiling surface to decide what to optimize, and (in a verified setting)
gating proof investment on measured wins. We found no comparable write-up;
the ecosystem knowledge mostly lives in Zulip threads.

## Why look at the emitted C at all

Performance intuitions imported from other languages routinely fail on Lean.
Our own first theory for the ChaCha20 bottleneck — "the round function
allocates ~250 tuples and structures per block" — was wrong, and a grep of
the emitted C settled it in seconds: the compiler had already eliminated every
tuple (case-of-known-constructor) and was updating the 16-word state structure
in place (exclusivity-checked reuse). The actual costs were elsewhere: function
calls that didn't inline, numbers that were secretly heap objects, and an
out-of-line runtime call behind an ordinary method name (`ByteArray.push`).
None of that is visible from the Lean source. All of it is visible in the C.

## The workflow

### 1. Find the emitted C

`lake build` writes one C file per Lean module to
`.lake/build/ir/<Module/Path>.c` (e.g.
`.lake/build/ir/LeanChachaPoly/Fast/ChaCha20.c`). It is readable: one
`LEAN_EXPORT lean_object* lp_…_FunctionName(…)` per definition, SSA-style
locals (`x_1, x_2, …`), runtime operations by name. You do not need to read
it linearly — you grep it.

### 2. Profile allocations by grep, not assumption

```
grep -c lean_alloc_ctor .lake/build/ir/Your/Module.c
```

gives the module's allocation-site count. For us: **3** in all of ChaCha20.c,
against a mental model predicting hundreds per block. Then locate each site
and read its surrounding branch: a `lean_is_exclusive(x)` test before the
allocation means the compiler emitted an in-place-reuse branch (functional-
but-in-place), so the allocation only fires when the value is shared. Our
`doubleRound` allocates only when its input state is shared — i.e. effectively
never inside the hot `rounds` loop, but once per block in `block` itself,
because `block` kept the initial state alive across the call (`addSt (rounds
10 s) s` holds `s` twice → refcount 2 → the first double-round must copy).

### 3. Read argument types in the signatures

Unboxed scalars appear as `uint32_t`/`uint8_t`/`size_t`. A `lean_object*`
parameter for something that is morally a number means **boxed `Nat`
arithmetic** in the loop — confirm by finding the matching `lean_nat_add` /
`lean_nat_dec_eq` / `lean_nat_sub` calls. This is how we found that our
fused XOR loop was building a heap-tracked successor index per byte
(`lean_byte_array_fget(m, i)` + `lean_nat_add(i, 1)` per output byte).

Corollary: if you want scalars to live in registers across a loop, make them
**parameters of a tail-recursive function**. Lean compiles tail recursion to a
`goto _start` loop with locals; a 16-field structure threaded through calls
round-trips through heap fields instead (16 `lean_ctor_get_uint32` + 16
`lean_ctor_set_uint32` per call). Our `roundsGo` carries the 16 ChaCha20 state
words as 16 `UInt32` parameters for exactly this reason — the same pattern
that made the Poly1305 limb engine fast (5 `UInt64` limb parameters).

### 4. Distinguish inline operations from runtime calls

Check the declaration in
`~/.elan/toolchains/<toolchain>/include/lean/lean.h`:

- `static inline` (e.g. `lean_byte_array_fget/uget/fset/uset`,
  `lean_ctor_get_uint32`) costs a few instructions at the call site.
- `LEAN_EXPORT` (e.g. `lean_byte_array_push`) is an out-of-line function call
  per invocation, with whatever checks it performs inside (for `push`:
  exclusivity + capacity).

This single distinction motivated our biggest Phase D win: replacing a
push-per-byte writer (64 runtime calls per 64-byte block) with
`ByteArray.set` stores into a pre-sized buffer (zero out-of-line calls per
byte). Register-threading alone measured 1.13x; with the set-based writer the
combination measured 1.58x.

### 5. Verify the optimized shape actually landed

After a change, re-read the new function's C. What good looks like:

- a tail-recursive worker = unboxed params + `goto _start` + (at most) one
  `lean_alloc_ctor` at the exit;
- an in-place writer = inline `fget`/`fset` only, zero allocations, zero
  `lean_inc`/`lean_dec` attributable to your wrappers (this confirmed our
  `SizedBA n` subtype — `{ o : ByteArray // o.size = n }` — is fully erased
  by the trivial-structure optimization: carrying a size invariant for the
  proofs costs nothing at runtime);
- tells that something went wrong: `lean_ctor_get_*`/`lean_ctor_set_*` pairs
  (heap round-trips), a self-call instead of `goto _start` (tail call not
  recognized), boxed `lean_object*` where you expected a scalar.

### 6. Measure before proving (the verified-setting discipline)

In a verified codebase the expensive resource is **proof effort**, so gate it
on measured wins. Our pattern, used in every phase:

1. Prototype the new engine in a `/tmp` scratch package compiled with the
   pinned toolchain and linked against the repo's own built objects
   (`.lake/build/ir/**/*.c.o.export`), so baseline and prototype run in the
   same binary, with the bench harness pattern from `Bench/Main.lean` and
   differential checks against the existing implementation at block-boundary
   lengths.
2. Set a numeric gate *before* measuring (ours: keep only if ≥1.2x at 64 KiB).
3. Only transcribe the bridge proofs for variants that pass.

The gate mattered immediately: Phase D's "obvious" optimization
(register-threading the rounds) measured 1.13x alone — below the gate — and
would have been a misdirected proof investment without the measurement.

## What kind of speedups these are (and aren't)

It's worth being precise, because the three optimization phases are not the
same kind of thing:

- The **Poly1305 limb engine** (Phase B) is an *algorithmic* change — the
  radix-2²⁶ representation with the `2¹³⁰ ≡ 5` wrap folded into the products
  is what every production implementation (poly1305-donna) uses, in any
  language. It came with genuinely new verified mathematics (the schoolbook-
  product wrap identity, carry-chain correctness).
- The **ChaCha20 phases** (C and D) are *not* algorithmic — the ARX operation
  count is unchanged. They remove overhead the Lean runtime adds that C never
  had: heap-boxed state between non-inlined calls (in C, locals are registers
  automatically; in Lean this must be forced by making them parameters) and
  the out-of-line `push` call per byte (C has no push/set distinction — you
  just store to a buffer). The *target shape* — 16 words in registers across
  20 rounds, output written once into a pre-sized buffer — is the canonical
  scalar ChaCha20 shape in any language. So the transformation is
  Lean-specific; the resulting machine-code shape is universal.
- The measured **magnitudes are machine-specific** (Apple Silicon here);
  the directions are not. Nothing exploits an M-series feature — no SIMD, no
  special instructions. One genuine caveat: x86-64 has 16 general-purpose
  registers vs arm64's 31, so the 16-words-in-registers loop will spill
  somewhat there; expect a smaller but still positive win.
- The remaining gap to scalar C (~1–2 GB/s vs our ~530 MB/s) is more
  Lean-runtime overhead (refcount traffic and per-call dispatch), not
  algorithm. The boxed-`Nat`-index overhead has been removed: `USize` indexing
  (`uget`/`uset`) behind a `msg.size < USize.size` guard measured +11% on full
  blocks (476 → 530 MB/s at 64 KiB, 7-run mean), at ~70 lines of bridge glue —
  the `uget`/`uset` operations reduce to the `getElem`/`set` engine pointwise
  (`Array.uset_eq_set`/`ugetElem_eq_getElem`), so the USize engine equals the
  set engine under the guard and inherits the capstone with no new spec
  reasoning. Indexing must stay in `USize` to win: a first cut that converted
  `(i+k).toUSize` per access measured ~0% (it only trades `fget`'s unbox for an
  added `usize_of_nat`); threading a once-per-block `USize` base is what landed
  the +11%. On a single 64-byte block the USize and set passes are even within
  run-to-run noise (the guard and base
  setup are not amortized over one block).
- After that, two further scalar candidates that stay within the trust boundary
  were prototyped in-tree, measured (7-run mean), and reverted below a 5% gate —
  a worked example of the measure-first rule paying off by *not* spending proof
  effort:
  - Threading the `USize` block base through the loop (carry `offU : USize`,
    increment it in `USize`, skip the per-block `off.toUSize`): **+1%**. The
    emitted C had already shown why — `setBlockXorU` does exactly one
    `lean_usize_of_nat` per 64-byte block, then per byte only `usize_add` +
    `uget` + `uset` + arithmetic. Reading the C answered this before the
    prototype; the measurement confirmed it.
  - Replacing the `copySlice` pre-fill (a memcpy that reads `msg`, whose bytes
    are then fully overwritten) with a zero-fill that doesn't read `msg`:
    **−22%**. There is no packed-`ByteArray` zero-allocator in core or
    Batteries; `⟨Array.replicate n 0⟩` lowers to `lean_mk_array` — a *boxed*
    `Array UInt8`, not a `lean_sarray` memset — so it is slower than the
    memcpy. The `copySlice` is the cheap way to materialize a sized buffer in
    safe Lean.

  Conclusion: the fused pass is at its scalar floor in safe Lean. The remaining
  gap to C is the byte-at-a-time stores (64 `uset`/block where C does 16 word
  stores) and the pre-fill pass — both need a trusted word-wide load/store (or
  uninitialized-alloc) `@[extern]` primitive, or SIMD. The ARX rounds are not
  the ceiling: scalar C runs the same rounds and reaches ~1–2 GB/s (vs our
  ~530 MB/s) on identical mixing — so what separates us from it is the per-byte
  load/store path, not the compute.

## Robustness to future compiler versions

Is this overfitted to today's compiler? The exposure is asymmetric:

- **Correctness is immune by construction.** The bridge theorems are about the
  functions' pure semantics; codegen and runtime changes can shift ns/op but
  can never invalidate an equivalence capstone.
- **The contingent piece is the set-vs-push gap**, which exists because `push`
  happens to be an exported runtime call today. If a future toolchain inlines
  it, note the failure mode: the set pass doesn't get slower — the retained
  push pass gets faster. The optimization becomes redundant, not harmful.
- **The robust piece is the shape.** Tail recursion → loop and unboxed scalar
  parameters → locals are among the most stable properties of any functional-
  language compiler. And code already in "registers + in-place stores" shape
  is what compilers optimize *toward*; a smarter future compiler compiles it
  at least as well, and might compile the old shape equally well (again:
  redundancy, not harm). Overfitting would be code that is fast only because
  of a quirk and slow once the quirk is fixed; nothing here has that
  structure.
- **The structural hedge**: every superseded engine is retained, proven equal
  (`chacha20_eq_pushPass`, `chacha20_eq_twoPass`, `accumulate_eq_accumulateNat`),
  differentially tested, and benchmarked in a permanent row. A toolchain bump
  that reshuffles the performance landscape shows up in `lake exe bench` as
  engine-vs-engine deltas, and swapping the production body to whichever
  proven-equal engine wins is a one-line edit plus a capstone-proof-body swap
  of a shape this repo has now executed twice.
- **Where the actual version-fragility lives**: the proofs, not the performance.
  Toolchain bumps historically churn lemma names, statement forms
  (`List.take_append` changed shape once already), and tactic budgets. Each
  optimization phase adds bridge surface (~300 lines for Phase D) to that
  maintenance cost. The benchmark surviving a compiler upgrade is the easy
  part; the proofs elaborating unchanged is the part to watch.

## What Phase D meant for this artifact

Ranked against the artifact's value ordering (security towers > spec
correctness > bridge methodology > raw throughput), Phase D contributes to the
third and fourth slots only — but its contribution to the third is real:

- It is the first **in-place mutation** code under a capstone here. Everything
  verified earlier was persistent-style code — push-based, append-only,
  structurally close to the list spec. Phase D bridges `ByteArray.set` writes
  into a pre-sized buffer, with the size invariant carried in an erased
  subtype — the shape production crypto code has, and semantically the
  trickiest to bridge (`set` doesn't compose like `++`; hence the splice kit
  in `Fast/Bridge/ChaCha20.lean`). If the question is "does this proof style
  handle imperative-shaped implementations, not just functional ones?",
  Phase D is the artifact's answer. Put sharply: the limb engine changed the
  *math* being verified; Phase D changed the *kind of code* being verified.
- It adds **zero new verified mathematics** — unlike the limb engine, its
  proofs are about Lean data structures, not about ChaCha20.
- It strengthens the artifact's **credibility on its performance claim**. An
  earlier audit of this repo deleted a "Native" layer whose equivalence
  theorems were vacuous wrappers; the verified fast implementation is the
  response, and it has to be non-toy to count. AEAD at ~344 MB/s is in
  "actually deployable on a single core" territory, and each superseded
  engine retained with an engines-agree theorem is evidence the bridge
  methodology survives optimization pressure: three substantial rewrites of
  the same function under an unchanged capstone.
- It recorded a **negative result** (the allocation theory, and the 1.13x
  sub-gate measurement for register-threading alone) that is arguably worth
  more to future maintainers than the 1.58x itself.
- The `USize`-indexing win (+12%) was first estimated at ~200 proof lines and
  deferred on that basis. The estimate was wrong: because `uget`/`uset` reduce
  to the `getElem`/`set` engine pointwise, the USize engine is provably equal
  to the set engine under the guard rather than re-derived against the spec, so
  it cost ~70 lines and inherits the capstone unchanged. It was then
  implemented (ChaCha20 476 → 530 MB/s at 64 KiB). The lesson is about the
  estimate, not the stopping rule: gate proof effort on a measurement, but
  re-estimate the effort when a reduction to existing lemmas is available.
