# lean-chacha-poly

A machine-checked **Lean 4** verification of RFC 8439 **ChaCha20-Poly1305 AEAD** —
the AEAD cipher suite preferred by TLS 1.3, WireGuard, and SSH.

It verifies three complementary layers:

1. **Functional correctness** — the spec computes the right bytes (it matches the RFC
   test vectors) and `decrypt ∘ encrypt = id`.
2. **Information-theoretic security** — Poly1305 is an almost-universal hash, so a
   forger's success probability is bounded by `8⌈L/16⌉ / 2¹⁰⁶`. The bound holds
   against every deterministic forger as a theorem, not a prose argument: a forger
   is a function `A` from the observed tag to a forged `(message, tag)`, and
   `poly1305_adversary_forgery_prob` bounds the fraction of consistent clamped keys
   it forges; `poly1305_adversary_forgery_multi_prob` adds the `v`-attempt union
   bound `v · 8⌈L/16⌉ / 2¹⁰⁶`. The bound involves no computational hardness
   assumption; its one mathematical hypothesis, the primality of `2¹³⁰ − 5`, is
   discharged by an axiom-free Lucas/Pratt certificate (`prime_P`), so the bounds
   are unconditional.
3. **A verified fast implementation** — a `ByteArray`-based implementation
   (`LeanChachaPoly/Fast/`) proved equal to the spec on *every* input
   (`chacha20_eq_spec`, `poly1305_eq_spec`, `encrypt_eq_spec`, `decrypt_eq_spec`),
   so the RFC vectors, the roundtrip theorem, and the forgery bounds all transfer
   to the code you would actually run.

Everything is `sorry`-free and rests on Lean/Mathlib's three foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`) — with a single, explicitly documented
exception (the `bv_decide` SAT-certificate axiom behind the quarter-round bijection).

```
lake exe cache get      # fetch the matching Mathlib build
lake build              # check every proof  (0 sorry)
lake exe test           # run the RFC 8439 vectors + property checks (spec AND fast)
lake exe bench          # local throughput benchmarks, fast vs spec
```

Lean toolchain `v4.29.1`, Mathlib pinned to match.

## Capstone results

### Poly1305 — security (the headline)

| Theorem | File | Statement |
|---|---|---|
| `poly1305_tag_forgery_prob` | `Poly1305/Security` | **The headline.** The published Poly1305 forgery probability, stated directly about `poly1305` and its 16-byte tags: with `r` uniform over the `2¹⁰⁶` clamped keys, turning an observed tag on `M` into a tag on `M' ≠ M` succeeds with probability at most **`8·max ⌈\|M\|/16⌉ ⌈\|M'\|/16⌉ / 2¹⁰⁶`**, with `⌈L/16⌉` written as `(L+15)/16`. The proof derives the cancellation of the one-time pad `s` from the two tag equations. |
| `poly1305_tag_forgery` | `Poly1305/Security` | The counting form: at most `8⌈L/16⌉` clamped keys admit any pad `s` producing the observed/forged tag pair. |
| `poly1305_adversary_forgery_prob` (+ `_multi_prob`) | `Poly1305/Security` | The adversary-as-function form: for any forger `A : tag → (message, tag)` with `(A t).1 ≠ M`, the fraction of clamped keys consistent with the observed tag under which `A` forges is at most the headline `ε`; `_multi` unions `v` attempts into `v · 8⌈L/16⌉ / 2¹⁰⁶`. Quantifies the bound over every deterministic attacker. |
| `poly1305_byte_forgery` | `Poly1305/Security` | The byte-level engine: a forger targeting a fixed accumulator offset mod `2¹²⁸` succeeds for at most `8 · max #blocks` keys; the factor `8` counts the integer candidates per offset. |
| `clampImage_card` / `clamp_fiber_card` | `Poly1305/Spec/Clamp` | The clamped key space has exactly `2¹⁰⁶` elements (the ε denominator), and every clamped value has exactly `2²²` preimages — so the uniform distribution on clamped keys is the one that drawing 16 uniform bytes and clamping produces. |
| `poly1305_almost_universal` | `Poly1305/Security` | Almost-universal hashing over the field `ZMod P`: two distinct block-lists collide for at most `max #blocks` keys `r` (root-counting on a nonzero difference polynomial). |
| `toBlocks_inj` (→ `poly1305_almost_universal_msg'`) | `Poly1305/Injectivity` (→ `Security`) | The `2^(8·len)` padding makes the message→block encoding injective, lifting the bound from block-lists to **distinct messages**. |
| `accumulate_eq_poly` | `Poly1305/Spec/Accumulate` | The iterative MAC loop **is** polynomial evaluation in `GF(2¹³⁰−5)` — the bridge the whole security argument rests on. |
| `poly1305_value` | `Poly1305/Spec/Tag` | The 16-byte tag reads back as exactly `(accumulate + s) mod 2¹²⁸` (serialization is faithful, not lossy) — the link between the forgery bound and the tag bytes themselves. |
| `prime_P` | `Poly1305/Spec/Primality` | `2¹³⁰ − 5` is prime, by an axiom-free Lucas/Pratt certificate (kernel `decide` over a fuel-based `powMod` — no `native_decide`). Supplies `Fact (Nat.Prime P)`, so the `ZMod P`-field security bounds are unconditionally instantiable. |

### ChaCha20 — correctness & structure

| Theorem | File | Statement |
|---|---|---|
| `chacha20_involutive` | `ChaCha20/Correctness` | Encrypting twice returns the message — encrypt = decrypt for a XOR stream cipher. |
| `quarterRound_bijective` | `ChaCha20/Spec/Permutation` | The quarter round is a bijection of `UInt32⁴` (with explicit inverse) — why ChaCha20 is permutation-based. |
| `keystream_counter_shift` | `ChaCha20/Spec/Seek` | CTR seekability: the keystream is random-access by 64-byte block. |

### AEAD — correctness & authenticity

| Theorem | File | Statement |
|---|---|---|
| `aead_forgery_prob` | `Aead/Security` | **Where the towers meet.** With the one-time poly key uniform over the clamped keys (the ChaCha20-PRF idealization — the one computational assumption, stated as a hypothesis), an attacker who modifies `(aad, ciphertext)` produces an accepted forgery with probability at most `8·max ⌈L/16⌉ ⌈L'/16⌉ / 2¹⁰⁶` over the `macData` lengths. |
| `decrypt_encrypt` | `Aead/Correctness` | The roundtrip: `decrypt (encrypt pt aad) aad = some pt`. |
| `decrypt_verifies` (+ `decrypt_accepts`) | `Aead/Security` | Verify-before-decrypt: plaintext is released only when the recomputed Poly1305 tag matches — acceptance of a forgery forces exactly the tag equation the forgery bound counts. |
| `macData_inj` | `Aead/Security` | The RFC §2.8 length-framed MAC input is injective in `(aad, ciphertext)`, so any change to either changes the authenticated input. |

### Fast implementation — equivalence bridges

| Theorem | File | Statement |
|---|---|---|
| `chacha20_eq_spec` | `Fast/Bridge/ChaCha20` | The `ByteArray` ChaCha20 produces exactly the spec's bytes on every input. The round bridge never reasons about ARX semantics: the fast rounds apply the spec's `quarterRound` terms verbatim, so each position is a definitional "stuck match" identity — no `bv_decide`. |
| `poly1305_eq_spec` | `Fast/Bridge/Poly1305` | The `ByteArray` Poly1305 produces exactly the spec's 16-byte tag on every input (the accumulation *is* `Spec.step`; the bridge is entirely about byte loads and blocking). |
| `encrypt_eq_spec` / `decrypt_eq_spec` | `Fast/Bridge/Aead` | The fast AEAD equals the spec — including rejecting exactly the same forgeries — so the security capstones apply verbatim to the fast code. |
| `decrypt_encrypt` (fast) | `Fast/Bridge/Aead` | The fast-side roundtrip, inherited from the spec capstone through the bridges. |

The fast implementation is Mathlib-free (it links into the `test` and `bench`
executables); the bridge proofs live in `Fast/Bridge/` and are compile-time only.
The Poly1305 engine is poly1305-donna-style 5×26-bit limb arithmetic in unboxed
`UInt64` — zero heap allocation per block; the only GMP work is once per message.
Its per-block correctness (`stepLimbs`, `Fast/Bridge/Poly1305Limb.lean`) isolates
the two non-linear facts — the 5×5 schoolbook product with the `2¹³⁰ ≡ 5` wrap
(`ring`) and the carry-chain value identity (`omega`) — with everything else
linear arithmetic over the limb bounds.

The Phase A GMP-`Nat` engine is retained as `accumulateNat` with its own
spec-equivalence theorem (`accumulateNat_eq`) and the corollary that the two
engines agree on every input (`accumulate_eq_accumulateNat`).

The fast ChaCha20 is a fused single pass: each 64-byte block is computed with
the 16 state words register-threaded through the round loop (`roundsGo` — the
words are loop parameters, so the compiled loop keeps them in registers) and
XOR-written in place into a pre-sized output with `ByteArray.set` — no
intermediate keystream buffer, one allocation per block. The push-based pass
(`chacha20Push`) and the two-pass composition (`xorBytes` + `keystream`, which
the key derivation needs) are retained with corollaries that the engines agree
on every input (`chacha20_eq_pushPass`, `chacha20_eq_twoPass`).

Indicative local throughput (`lake exe bench`, Apple Silicon, 64 KiB messages):
ChaCha20 ~475 MB/s fast (in-place set pass) vs ~340 MB/s for the retained
push pass vs ~220 MB/s for the retained two-pass vs ~14 MB/s spec; Poly1305
~1.1 GB/s fast (limb engine) vs ~17 MB/s for the retained Nat engine vs
~3 MB/s spec; AEAD ~320 MB/s fast vs ~2 MB/s spec.

These optimizations were driven by reading the **emitted C**
(`.lake/build/ir/**.c`) rather than by intuition — the first theory about the
ChaCha20 bottleneck was wrong, and a grep settled it. The full workflow
(profiling allocations and boxing by grep, the `static inline` vs
`LEAN_EXPORT` runtime distinction, verifying the optimized shape landed,
measure-before-prove gating), plus a discussion of which speedups are
algorithmic vs Lean-runtime-specific and how the design holds up under future
compiler versions, is written up in
[docs/optimizing-lean-runtime.md](docs/optimizing-lean-runtime.md) — it
should transfer to any Lean 4 project with a hot path.

The spec is directly executable: the test suite (`lake exe test`) runs it against the
RFC 8439 vectors, runs the same vectors through the fast implementation, and
differentially checks fast against spec on block-boundary lengths. It also runs the
316 Wycheproof ChaCha20-Poly1305 cases with a 96-bit nonce (`Tests/WycheproofTest.lean`,
256 `valid` + 60 `invalid`: modified tags, edge-case ciphertexts and Poly1305 keys,
truncations) through both the spec and the fast implementation — adversarial coverage
of the one leap the proofs cannot reach, that the spec matches RFC 8439.
`Tests/AxiomGuard.lean` re-checks every capstone's axiom set at compile time (the build
fails if one silently grows).

## How length/size invariants are encoded

All length constraints live in the **types**, via `{ x // p x }` subtypes
(`LeanChachaPoly/Subtypes.lean`): a `Key` is `Bytes 32`, a ChaCha20 `State` is
`Words 16` (a size-16 `Array`, accessed totally — no panicking `!`-indexing), a full
Poly1305 block is `Bytes 16`, the MAC input is `Padded` (length `% 16 = 0`). Functions
take and return these, so length guarantees are checked by the compiler rather than
threaded as proof arguments or trusted.

## Layout

```
LeanChachaPoly/
  Subtypes.lean              Bytes n / Words n / Padded  (length-indexed types)
  ChaCha20/
    Spec.lean                definitions
    Correctness.lean         chacha20_involutive / chacha20_length       ← capstone
    Spec/{QuarterRound, Keystream, Seek, Permutation, Xor}.lean
  Poly1305/
    Spec.lean                definitions + basic properties
    Security.lean            security tower → tag-level forgery prob     ← capstone
    Injectivity.lean         block-encoding injectivity → toBlocks_inj   ← capstone
    Spec/{Sum, Blocking, Accumulate, Tag, Clamp}.lean
  Aead/
    Spec.lean                construction (encrypt / decrypt)
    Correctness.lean         decrypt_encrypt (the roundtrip)             ← capstone
    Security.lean            verify-before-decrypt → AEAD forgery bound  ← capstone
    Spec/{KeyDerivation, MacData}.lean
  Fast/
    Types.lean               BytesA n (ByteArray subtype) + spec conversions
    ChaCha20.lean            unboxed 16-word state, fused keystream-XOR pass
    Poly1305.lean            5×26-bit UInt64 limb engine (+ Nat-engine baseline)
    Aead.lean                fast AEAD composition
    Bridge/{ByteList, ChaCha20, Poly1305, Poly1305Limb, Aead}.lean  fast = spec  ← capstones
Tests/                       RFC 8439 vectors (spec + fast) + differential + axiom guard
Bench/                       lake exe bench — fast vs spec throughput
```

Every theorem's doc-comment is tagged `**Capstone**`, `**Key lemma**`, or
`**Supporting**` so its importance is visible at a glance.

## What is NOT covered (and why)

This project proves what is *provable in Lean about the algorithm*. It deliberately does
**not** claim the following:

- **ChaCha20 confidentiality / PRF security.** "The keystream is indistinguishable from
  random" is a *computational* assumption requiring a probabilistic game framework
  (adversaries, advantage, reductions). It is not a theorem one can prove in plain Lean
  about the function — it is out of scope by nature. What *is* proved is the structural
  fact (`quarterRound_bijective`) that ChaCha20 is permutation-based. The AEAD forgery
  bound (`aead_forgery_prob`) isolates this assumption as its model hypothesis: it
  quantifies over a uniform one-time poly key, which is exactly what the PRF assumption
  would supply for `derivePolyKey`.

- **Primality of `P = 2¹³⁰ − 5`** *(discharged).* The field-level forgery bounds need
  `ZMod P` to be a field, i.e. `P` prime. This 40-digit primality is proved by an
  axiom-free Lucas/Pratt certificate (`prime_P`, `Poly1305/Spec/Primality.lean`), whose
  `instance : Fact (Nat.Prime P)` the security theorems resolve directly — they carry no
  primality hypothesis and are unconditional statements. The certificate's modular
  exponentiations are evaluated by the *kernel*
  through a fuel-based `powMod` and plain `decide`, so it adds no axiom (`#print axioms
  prime_P` is `[propext, Classical.choice, Quot.sound]`) — see
  [docs/primality-certificate.md](docs/primality-certificate.md).

- **One trusted axiom.** `quarterRound_bijective` (and its two round-trips) are proved
  by `bv_decide`. The SAT solver itself is *untrusted* — it must produce an LRAT
  certificate, which a checker *formally verified in Lean* validates. The trust enters
  at one point: that checker is run as natively compiled code rather than by the kernel
  (infeasible at this size), so the Lean compiler/runtime joins the trusted base for
  exactly that one Boolean evaluation — recorded as a per-theorem axiom of the form
  `…bv_decide.ax` ("the verified checker returned `true` on this certificate"), pinned
  by the axiom guard. An algebraic reproof (from the rotate/XOR invertibility lemmas
  already present) would remove even that — see future work.

- **Constant-time / side-channel resistance.** The proofs are about input→output values;
  they say nothing about timing, caches, or power. The fast implementation — the code
  that actually runs — compares tags with a whole-tag `ctEq` (equal sizes and a zero
  OR-accumulation of per-byte XORs), scanning every byte with no first-mismatch branch;
  `Fast.Bridge.Aead.decrypt_eq_spec` proves it computes the same function as the spec.
  (The spec's reference `decrypt` keeps a short-circuiting `==` for readability, with
  `decryptCT`/`decryptCT_eq_decrypt` the spec-level constant-time variant.) This removes
  the source-level short-circuit but is not a hardware guarantee: constant-time execution
  of the compiled comparison is a compiler/CPU property outside Lean's evaluation model.

- **Nonce-reuse safety and message-length limits.** Reusing a `(key, nonce)` pair is
  catastrophic for Poly1305, and the 32-bit block counter wraps on messages over
  `2³² · 64` bytes ≈ 256 GiB (`keystream`'s docstring), silently reusing keystream.
  Both are *usage* constraints the types do not enforce; no theorem carries them as
  hypotheses.

- **Compiler trust for execution.** The fast implementation is proved equal to the spec
  as Lean functions; as for any verified-then-compiled program, the Lean compiler and
  runtime executing it are trusted (the proofs are about the functions, not the emitted
  machine code).

## Future work

- Reprove `quarterRoundInv_quarterRound` / `quarterRound_quarterRoundInv` algebraically
  (via `rotl32_inv` / `rotl32_xor` / `xor_self_cancel`) to make the whole library
  uniformly foundational — no `bv_decide` axiom.
- Speed up the fast ChaCha20 further (still the AEAD bottleneck at ~475 MB/s
  vs the limb Poly1305's ~1.1 GB/s): the remaining measured scalar win is
  `USize` indexing (~+12%, prototyped), which needs a `msg.size < USize.size`
  guard branch and substantial bridge glue; SIMD is outside Lean's current
  reach.
- Upstream the generic bridge lemmas (the `ByteArray ↔ List` kit,
  `bitConstrained_card`, `zipWith_take_right`) to Batteries/Mathlib to shrink the
  project-local surface — candidates and locations in
  [docs/upstream-candidates.md](docs/upstream-candidates.md).

## References

- RFC 8439 — *ChaCha20 and Poly1305 for IETF Protocols* (June 2018)
- D. J. Bernstein, *ChaCha, a variant of Salsa20* (2008)
- D. J. Bernstein, *The Poly1305-AES message-authentication code* (2005)
- [primefactor-io/xchacha20-poly1305](https://github.com/primefactor-io/xchacha20-poly1305)
  — the RFC-vector `Tests/` are a 1:1 port of this Go implementation's test files (the RFC
  8439 vectors themselves are from the RFC).
- [C2SP/wycheproof](https://github.com/C2SP/wycheproof) — `testvectors_v1/chacha20_poly1305_test.json`,
  the source of `Tests/WycheproofTest.lean` (the 96-bit-nonce cases).
