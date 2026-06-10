# Development history — the path taken

This is a retrospective of how `lean-chacha-poly` reached its current state. For *what*
is proved and *how to use it*, see [`README.md`](README.md). The project is complete:
`lake build` is `sorry`-free, the RFC 8439 vectors pass, and the capstones are
axiom-clean (modulo one documented `bv_decide` axiom).

> **Correction to the original scope.** The first design notes described this as an
> "axiom-free, Mathlib-free" project with security "out of scope." That turned out to be
> too pessimistic: the Poly1305 *information-theoretic* security results **are** provable
> in Lean and now form the centerpiece (using Mathlib's `Polynomial`/`ZMod`). The only
> non-foundational axiom is the `bv_decide` SAT-certificate behind the quarter-round
> bijection.

## Stage 1 — Functional correctness

Defined the three primitives over `List UInt8` and proved the functional capstones:

- ChaCha20: keystream-length correctness + XOR cancellation ⇒ `chacha20_involutive`
  (encrypt = decrypt) and `chacha20_length`.
- AEAD: `decrypt_encrypt` (the roundtrip) by algebraic assembly — `encrypt` emits
  `ct ‖ tag`, `decrypt` splits it, recomputes the same tag, and re-applies the ChaCha20
  involution.
- **Native bridges** (since removed): a `ByteArray` wrapper per primitive with
  `*_eq_spec` theorems. An external audit later found these definitional — the wrapper
  *was* the spec, so the bridge theorems were tautologies — and the layer was deleted
  (see Stage 5). A meaningful implementation-equivalence theorem awaits an
  independently written fast implementation.

Validated against the RFC 8439 test vectors (`Tests/`).

## Stage 2 — Information-theoretic security (the centerpiece)

Built the Poly1305 unforgeability argument as a tower:

1. `accumulate_eq_poly` — the iterative MAC loop equals polynomial evaluation in
   `GF(P)`, `P = 2¹³⁰ − 5` (`Spec/Accumulate.lean`).
2. `accumulate_cast_eq_eval` — recast in `ZMod P`: the accumulator is `(msgPoly B).eval r`.
3. `poly1305_almost_universal` — over the field, two distinct block-lists collide for at
   most `max #blocks` keys `r`, because a colliding `r` is a root of a nonzero difference
   polynomial and a degree-`n` polynomial has ≤ `n` roots (`Polynomial.card_roots'`).
   Field-ness needs `P` prime, taken as `[Fact (Nat.Prime P)]`.
4. `poly1305_almost_delta_universal` + `collision_union_bound` + the ≤ 8 candidate count
   ⇒ `poly1305_byte_forgery`: the byte-level bound `8·⌈L/16⌉`.
5. `clampImage_card` (`Spec/Clamp.lean`): the clamp mask leaves `128 − 22 = 106` bits
   free, so the clamped key space has exactly `2¹⁰⁶` elements (a bit-counting bijection
   between submasks and Boolean assignments to the free bits). Dividing the byte-level
   count by it gives `poly1305_clamped_forgery_prob`: the published forgery probability
   `8⌈L/16⌉ / 2¹⁰⁶`.
6. `Injectivity.lean`: the `2^(8·len)` padding makes the byte→block encoding injective
   (`leVal_inj → blockToNat_inj/finalBlockToNat_inj → toBlocks_inj`), lifting the bound
   to distinct *messages*.

On the AEAD side: `decrypt_verifies` (verify-before-decrypt) and `macData_inj` /
`*_binding` (the RFC §2.8 length-framed MAC input is injective in `(aad, ciphertext)`).

## Stage 3 — Subtype standardization

Replaced three inconsistent ways of carrying length invariants (structures-with-proofs,
threaded proof parameters, and unchecked `!`-indexing) with one: `{ x // p x }` subtypes
in `Subtypes.lean` (`Bytes n`, `Words n`, `Padded`). `State` became `Words 16` with
*total* `get`/`set` (no panicking indexing); keys/blocks/tags/MAC-input carry their
length in the type. The analytic security tower was preserved behind a `blockNats` /
`toBlockNats` adapter so the migration didn't disturb the axiom-clean proofs.

## Stage 4 — Finalization

- **Reorg.** Surfaced capstone-grade results at each primitive's top level
  (`Correctness.lean` for functional correctness, `Security.lean` / `Injectivity.lean`
  for security), with supporting lemmas under `<Primitive>/Spec/`. Eliminated the
  "declared in Spec, proved elsewhere" split and the empty `Block.lean`.
- **Dedup / prune.** One shared `foldl_add_eq_sum` (was copied 4×); removed `rfl` no-op
  lemmas and unused characterizations.
- **Comments.** Every significant theorem tagged `**Capstone**` / `**Key lemma**` /
  `**Supporting**`; purged stale prose (the old "Mathlib-free / remaining gap / out of
  scope" notes).
- **Docs.** This file and a full `README.md`, including a "what is NOT covered"
  section.

## Stage 5 — Audit response

An external audit (2026-06-10) verified the headline claims but found the security
theorems stopped at the *accumulator* (the "s cancels" step was prose), the Native
bridges were definitional tautologies, and the Poly1305/AEAD towers never met.
Addressed in full:

- **Tag-level forgery theorem** (`poly1305_tag_forgery`, `_prob`): stated about
  `poly1305` and its 16-byte tags; the proof derives the cancellation of the one-time
  pad `s` by subtracting the two tag equations (via `poly1305_value`). Bounds stated
  as `8 · max ⌈|M|/16⌉ ⌈|M'|/16⌉` via the new `toBlockNats_length`.
- **The towers meet** (`aead_forgery_bound`, `aead_forgery_prob` in `Aead/Security`):
  `macData_inj` + the tag-level theorem give the AEAD forgery probability under the
  uniform-poly-key model hypothesis (= the ChaCha20-PRF idealization);
  `decrypt_accepts` ties acceptance to the counted tag equation.
- **Probability model closed** (`clamp_fiber_card`): every clamped value has exactly
  `2²²` preimages, so uniform 16-byte `r` through `clamp` is uniform on the clamped
  keys. The counting machinery was generalized (`bitConstrained_card`) to serve both
  this and `clampImage_card`.
- **Native layer deleted** (see Stage 1's note) — the wrappers were the spec itself,
  so the `*_eq_spec` theorems stated nothing.
- **Pruned** a dozen declarations that restated definitions, instantiated generic
  Mathlib facts, or were one-line contrapositives of retained lemmas; `clamp_rfc`
  strengthened to a complete characterization (cleared bits false **and** all other
  bits preserved).
- **Hygiene**: `Tests/AxiomGuard.lean` (`#guard_msgs` on `#print axioms` — the build
  fails if a capstone's axiom set grows), GitHub Actions CI, `.gitignore`.

## Current structure

```
LeanChachaPoly/
  Subtypes.lean
  ChaCha20/   Spec · Correctness             + Spec/{QuarterRound,Keystream,Seek,Permutation,Xor}
  Poly1305/   Spec · Security · Injectivity  + Spec/{Sum,Blocking,Accumulate,Tag,Clamp}
  Aead/       Spec · Correctness · Security  + Spec/{KeyDerivation,MacData}
Tests/        ChaCha20Test · Poly1305Test · ChaCha20Poly1305Test · PropertiesTest · AxiomGuard · Helpers
```

## Verification

- `lake build` — 0 `sorry`.
- `Tests/AxiomGuard.lean` — `#guard_msgs`-enforced `#print axioms` on every capstone:
  `{propext, Classical.choice, Quot.sound}`, plus the pre-existing
  `quarterRound …bv_decide.ax` pair (the lone non-foundational axiom). The build fails
  if any set grows.
- `lake exe test` — all RFC 8439 vector groups + property checks pass.
- CI (`.github/workflows/ci.yml`) runs all of the above on every push.

## Phase: verified fast implementation (2026-06)

A `ByteArray`-based implementation under `LeanChachaPoly/Fast/` (Mathlib-free, linked
into the executables), proved equal to the spec on every input:

- **ChaCha20** — unboxed 16-field `UInt32` state (`St`), rounds reuse
  `Spec.quarterRound` verbatim (inlined), keystream pushed into a
  capacity-reserved `ByteArray`. Bridge `chacha20_eq_spec`: the round bridge is a
  "stuck match" identity per quarter-round position (`Fast/Bridge/ChaCha20.lean`) —
  no bit-vector reasoning, no `bv_decide`.
- **Poly1305 (Phase A)** — message stays a `ByteArray`; 16-byte blocks loaded as two
  `UInt64` words combined into a `Nat`; the accumulation reuses `Spec.step` (GMP
  arithmetic) definitionally. Bridge `poly1305_eq_spec` via a little-endian valuation
  `leVal` and a `fun_induction` aligned with `toBlockNats`.
- **AEAD** — composition; bridges `encrypt_eq_spec` / `decrypt_eq_spec` and the
  inherited fast-side `decrypt_encrypt`.
- **Tests** — `Tests/FastTest.lean`: RFC vectors through the fast API + differential
  fast-vs-spec at block-boundary lengths (LCG inputs).
- **Bench** — `lake exe bench` (built in CI, run locally). Apple Silicon, 64 KiB:
  ChaCha20 ~207 MB/s fast vs ~14 MB/s spec; Poly1305 ~17 MB/s vs ~3 MB/s.
- All five bridge capstones are in the axiom guard with only the three foundational
  axioms (`poly1305_eq_spec` even avoids `Classical.choice`).

## Phase B: Poly1305 limb arithmetic (2026-06)

`accumulate` replaced by a poly1305-donna-style 5×26-bit limb engine in unboxed
`UInt64` (`Fast/Poly1305.lean`); the Phase A GMP-`Nat` engine survives as
`accumulateNat` (differential test + bench baseline). Capstone `poly1305_eq_spec`
kept its name, statement, and pinned axiom set `[propext, Quot.sound]`, so the
AEAD bridge, AxiomGuard, and vector tests needed zero changes.

- Engine: all-arithmetic (`+ * / %` with power-of-two literals — clang emits
  shifts/ands, and the form stays in `omega`'s fragment); 5 limb registers
  threaded through a tail-recursive `go`; invariant `hᵢ < 2²⁷`; the `2¹³⁰ ≡ 5`
  wrap folds into `sᵢ = 5·rᵢ` products (all intermediates < 2⁶¹); freeze =
  one `limbsToNat h % P` per message; trailing partial block = one `Spec.step`.
- Bridge (`Fast/Bridge/Poly1305Limb.lean` + rewritten accumulation section of
  `Fast/Bridge/Poly1305.lean`): per-block `stepLimbs` with equation-style
  intermediates discharged by `rfl` against the loop body's definitional
  let-fvars under `fun_induction`; the two non-linear facts isolated as
  `mul_wrap` (`ring`) and `carry_fixup` (`omega`); loop invariant is the frozen
  value, so no freeze lemma exists.
- Proof gotchas recorded: a single end-to-end `omega` over the assembled value
  identity diverges (>10 min) — stage the finish via `Nat.add_mul_mod_self_right`
  instead; `congr` on goals containing limb let-fvars exceeds `maxRecDepth` —
  rewrite the foldl seed with a targeted `have` instead; `UInt64.size` is an
  opaque atom to omega — `rw [show UInt64.size = 2^64 from rfl]` first.
- Bench (Apple Silicon): Poly1305 1.09–1.19 GB/s at 64 KiB–1 MiB (~70× Phase A,
  ~14 ns/block); AEAD 168–171 MB/s (from 15), now ChaCha20-bound.

## Phase C: fused ChaCha20 keystream-XOR pass (2026-06)

`chacha20` replaced by a fused single pass (`chacha20Go` in `Fast/ChaCha20.lean`):
each 64-byte block is computed in registers and XORed directly against the
message (`pushBlockXor` = 16 unrolled `pushXor4`; trailing partial block via
`tailXor` against one serialized scratch block) — no intermediate keystream
buffer. The two-pass composition (`xorBytes` + `keystream`) survives — the
key derivation needs `keystream` — with the engines-agree corollary
`chacha20_eq_twoPass` (differential test + bench baseline). Capstone
`chacha20_eq_spec` kept its name, statement, and pinned axiom set
`[propext, Classical.choice, Quot.sound]`, so the AEAD bridge, AxiomGuard,
and vector tests needed zero changes.

- Bridge (new fused-pass section of `Fast/Bridge/ChaCha20.lean`, still
  Mathlib-free): peel the spec keystream one block at a time
  (`keystream_block_cons`; bind the serialized-block length as a
  universally-quantified `have` first — instantiating `.property` with a
  metavariable inside `simp` whnf-times-out), split the spec XOR along the
  64-byte seams (`zipWith_block_split`, and `zipWith_seg` with explicit
  equation parameters so offsets stay in flat `off + 4k` form), match each
  4-byte `pushXor4` against one serialized word (`slice4_eq` peel), and close
  the main `fun_induction` by staging the split in a targeted `have` — no
  `congr` anywhere. `zipWith_take_right` (zipWith truncation) is not in
  core/Mathlib; proved by structural recursion.
- Bench (Apple Silicon): ChaCha20 ~295 MB/s at 1 KiB–1 MiB (~1.5× the retained
  two-pass ~200 MB/s); AEAD 231–238 MB/s (from 168–171), still ChaCha20-bound.

## Phase D: register-threaded rounds + in-place set-based writer (2026-06)

Emitted-C inspection overturned the "allocation in the round function" theory:
the compiler already eliminates the `quarterRound` tuples and updates `St` in
place when exclusive. The real overheads were 10 non-inlined `doubleRound`
calls/block round-tripping the 16 words through heap fields, and the per-byte
`ByteArray.push` runtime call (`set`/`get` are static-inline in the runtime;
`push` is an exported call). Two changes, prototype-measured before any proof
work (register-threading alone = 1.13x, below the 1.2x gate; combined = 1.58x):

- `roundsGo` — the 16 state words as loop *parameters* (16 uint32 locals in
  the compiled loop, one `St` allocation at exit); `block` fused end-to-end
  (init words as lets, `roundsGo 10`, add-back inline).
- Set-based writer — output pre-sized with one `copySlice` memcpy, then
  `setXor4`/`setBlockXor` XOR-write each block in place via `ByteArray.set`
  on a `SizedBA` subtype (zero-cost, erased); `chacha20SetGo` mirrors the
  push loop. Push pass retained as `chacha20Push` (+`chacha20_eq_pushPass`);
  two-pass and `chacha20_eq_twoPass` untouched.
- Bridge: `roundsGo_eq` (induction + the 8-rcases pattern),
  `block_eq_addSt_rounds` (so `block_toState` keeps its statement),
  splice kit (`toList_set`, `set4_splice`, `setXor4_toList`, `splice_step` —
  carries the accumulated segment length in the conclusion so the 16 steps
  chain with no length side conditions), `setBlockXor_toList`,
  `tailXorSet_toList`, `chacha20SetGo_toList`. Capstone `chacha20_eq_spec`
  name/statement/axioms unchanged → AEAD bridge/AxiomGuard/tests zero changes.
- Gotchas: 30+ `omega`s in one declaration exhaust the heartbeat budget — use
  shared term-proof helpers (`le_of_off64`); `rw [← List.drop_drop]` must be
  staged inside an isolated `have` (wrong occurrence in the main goal).
- Bench (Apple Silicon, 64 KiB): ChaCha20 476 MB/s (was 301, 1.58x; push pass
  338, two-pass 220); AEAD 316–335 MB/s (was 231–238). At 64 B the push pass
  is slightly faster (267 vs 301 ns — the `copySlice` init dominates tiny
  messages); AEAD there is Poly1305-dominated either way.

## Future work

- **Drop the last axiom.** Reprove the quarter-round round-trips algebraically (from
  `rotl32_inv` / `rotl32_xor` / `xor_self_cancel`) instead of `bv_decide`, making the
  whole library uniformly foundational.
- **Unconditional security.** Discharge `Nat.Prime (2¹³⁰ − 5)` via a Pratt certificate,
  removing the `[Fact (Nat.Prime P)]` hypothesis.
- **Faster ChaCha20.** Still the AEAD bottleneck (~475 MB/s vs limb Poly1305's
  ~1.1 GB/s): the remaining measured scalar win is `USize` indexing (~+12%,
  prototyped — needs a `msg.size < USize.size` guard branch with `chacha20Push`
  as the proven fallback, and ~150–250 lines of bridge glue); SIMD is outside
  Lean's current reach.
