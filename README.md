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
   to the code you would run.

Every theorem is `sorry`-free and rests only on Lean's three foundational axioms,
with capstones pinned in `Tests/AxiomGuard.lean`.

```
lake exe cache get      # fetch the matching Mathlib build
lake build              # check every proof  (0 sorry)
lake exe test           # RFC 8439 + Wycheproof vectors + property checks (spec AND fast)
lake exe bench          # local throughput benchmarks, fast vs spec
```

Lean toolchain `v4.29.1`, Mathlib pinned to match.

## Capstone results

For a referee's reading list — every result restated in plain vocabulary
and proved as a one-line corollary in one file — see
[`LeanChachaPoly/Statements.lean`](LeanChachaPoly/Statements.lean).

### Poly1305 — security

| Theorem | File | Statement |
|---|---|---|
| `poly1305_tag_forgery_prob` | `Poly1305/Security` | The published Poly1305 forgery probability, stated about `poly1305` and its 16-byte tags: with `r` uniform over the `2¹⁰⁶` clamped keys, turning an observed tag on `M` into a tag on `M' ≠ M` succeeds with probability at most `8·max ⌈\|M\|/16⌉ ⌈\|M'\|/16⌉ / 2¹⁰⁶`. |
| `poly1305_adversary_forgery_prob` (+ `_multi_prob`) | `Poly1305/Security` | The same bound quantified over every deterministic attacker: for any forger `A : tag → (message, tag)` with `(A t).1 ≠ M`, the fraction of consistent clamped keys under which `A` forges is at most `ε`; `_multi` unions `v` attempts into `v · 8⌈L/16⌉ / 2¹⁰⁶`. |
| `poly1305_almost_universal` | `Poly1305/Security` | The mathematical heart: over the field `ZMod P`, two distinct block-lists collide for at most `max #blocks` keys `r` (root-counting on a nonzero difference polynomial). |
| `prime_P` | `Poly1305/Spec/Primality` | `2¹³⁰ − 5` is prime, by an axiom-free Lucas/Pratt certificate (factor tree and witnesses in [docs/primality-certificate.md](docs/primality-certificate.md)). Supplies `Fact (Nat.Prime P)`, so the bound carries no primality hypothesis. |

The bound is the top of a tower: the MAC loop is polynomial evaluation
in `GF(2¹³⁰−5)` (`accumulate_eq_poly`), injective block encoding
lifts the collision bound to distinct messages (`toBlocks_inj`), the
`2¹⁰⁶`-element clamped key space with uniform fibers sets the denominator
(`clampImage_card`/`clamp_fiber_card`), and the tag reads back faithfully from
its bytes (`poly1305_value`). The same bound is also stated in Bernstein's
conditional form `Pr[forge | observed tag] ≤ ε` (`poly1305_tag_forgery_cond_prob`)
and at coarser normalizations (`poly1305_tag_forgery`, `poly1305_byte_forgery`).

### ChaCha20 — correctness & structure

| Theorem | File | Statement |
|---|---|---|
| `chacha20_involutive` | `ChaCha20/Correctness` | Encrypting twice returns the message — encrypt = decrypt for a XOR stream cipher. |
| `quarterRound_bijective` | `ChaCha20/Spec/Permutation` | The quarter round is a bijection of `UInt32⁴` (with explicit inverse) — why ChaCha20 is permutation-based. |
| `keystream_counter_shift` | `ChaCha20/Spec/Seek` | CTR seekability: the keystream is random-access by 64-byte block. |

### AEAD — correctness & authenticity

| Theorem | File | Statement |
|---|---|---|
| `aead_forgery_prob` | `Aead/Security` | The Poly1305 and AEAD towers joined. With the one-time poly key uniform over the clamped keys (the ChaCha20-PRF idealization — the one computational assumption, stated as a hypothesis), an attacker who modifies `(aad, ciphertext)` produces an accepted forgery with probability at most `8·max ⌈L/16⌉ ⌈L'/16⌉ / 2¹⁰⁶` over the `macData` lengths. |
| `decrypt_encrypt` | `Aead/Correctness` | The roundtrip: `decrypt (encrypt pt aad) aad = some pt`. |
| `decrypt_verifies` (+ `decrypt_accepts`) | `Aead/Security` | Verify-before-decrypt: plaintext is released only when the recomputed Poly1305 tag matches — acceptance of a forgery forces exactly the tag equation the forgery bound counts. |
| `macData_inj` | `Aead/Security` | The RFC §2.8 length-framed MAC input is injective in `(aad, ciphertext)`, so any change to either changes the authenticated input. |

### Fast implementation — equivalence bridges

| Theorem | File | Statement |
|---|---|---|
| `chacha20_eq_spec` | `Fast/Bridge/ChaCha20` | The `ByteArray` ChaCha20 produces the spec's bytes on every input. |
| `poly1305_eq_spec` | `Fast/Bridge/Poly1305` | The `ByteArray` Poly1305 produces the spec's 16-byte tag on every input. |
| `encrypt_eq_spec` / `decrypt_eq_spec` | `Fast/Bridge/Aead` | The fast AEAD equals the spec — including rejecting the same forgeries — so the security capstones transfer to the fast code. |
| `decrypt_encrypt` | `Fast/Bridge/Aead` | The fast-side roundtrip, inherited from the spec capstone through the bridges. |

The fast implementation imports no Mathlib — only core Lean and the spec — so
the `bench` executable links it without compiling or linking Mathlib, which is
confined to the compile-time bridge proofs in `Fast/Bridge/`.
The Poly1305 engine is poly1305-donna-style 5×26-bit limb arithmetic in
unboxed `UInt64`; the ChaCha20 engine is a fused single pass with the 16 state
words register-threaded through the round loop and the output XOR-written in
place via `USize` indexing (behind a `msg.size < USize.size` guard). Each
superseded engine — the GMP-`Nat` Poly1305 and the `getElem`/`set`, push-based,
and two-pass ChaCha20 — is retained with a corollary that the engines agree on
every input. How they were built and bridged, phase by phase, is in
[docs/plan.md](docs/plan.md).

Indicative local throughput — `lake exe bench`, mean of 7 runs on an Apple M2
(8-core, 16 GB, macOS 26.5.1, Lean v4.29.1), 64 KiB messages:

```
  name                       MB/s
  chacha20 fast (USize)       530      ← chacha20, the AEAD's ChaCha20 pass
  chacha20 fast set           476        retained getElem/set engine
  chacha20 fast push          341        retained push engine
  chacha20 fast 2pass         222        retained two-pass (keystream ⊕ msg)
  chacha20 spec                13
  poly1305 fast (limb)       1110      ← poly1305, the AEAD's MAC pass
  poly1305 fast nat            17        retained GMP-Nat engine
  poly1305 spec                 2
  aead encrypt/decrypt fast   345
  aead encrypt/decrypt spec     2
```

Magnitudes are machine-specific; `lake exe bench` prints the full table. The
ChaCha20 pass was tuned by reading the emitted C — the first theory about its
bottleneck was wrong. That workflow, and which speedups are algorithmic versus
Lean-runtime-specific, are in
[docs/optimizing-lean-runtime.md](docs/optimizing-lean-runtime.md).

The spec is directly executable. `lake exe test` runs the RFC 8439 vectors and
the 316 Wycheproof ChaCha20-Poly1305 cases (256 `valid` + 60 `invalid`) through
both the spec and the fast implementation, and differentially checks fast
against spec on block-boundary lengths — adversarial coverage of the one leap
the proofs cannot reach, that the spec matches RFC 8439. `Tests/AxiomGuard.lean`
re-checks every capstone's axiom set at compile time.

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
    Security.lean            security tower → adversary forgery bounds   ← capstone
    Injectivity.lean         block-encoding injectivity → toBlocks_inj   ← capstone
    Spec/{Sum, Blocking, Accumulate, Tag, Clamp, Primality}.lean
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
    Bridge/{ByteList, ChaCha20, Poly1305, Poly1305Limb, Aead}.lean
                             fast = spec                                 ← capstones
  Statements.lean            the capstones restated in one file (reading list)
Tests/                       RFC 8439 + Wycheproof vectors (spec + fast) + differential + axiom guard
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

- Speed up the fast ChaCha20 further. The ChaCha20 pass (~530 MB/s) is the AEAD
  bottleneck against the limb Poly1305's ~1.1 GB/s. Two further scalar
  candidates within the current trust boundary were prototyped, measured, and
  reverted below a 5% gate, leaving the pass at its scalar floor in safe Lean;
  closing the remaining gap to C's ~1–2 GB/s needs a word-wide `ByteArray`
  load/store (an `@[extern]` primitive the project declines on trust grounds) or
  SIMD, which Lean cannot emit. The measurements and the trust-boundary argument
  are in [docs/optimizing-lean-runtime.md](docs/optimizing-lean-runtime.md).
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
  8439 vectors themselves are from the RFC). Pinned at upstream HEAD `6bff6e2` as of 2026-06-11.
- [C2SP/wycheproof](https://github.com/C2SP/wycheproof) — `testvectors_v1/chacha20_poly1305_test.json`,
  the source of `Tests/WycheproofTest.lean` (the 96-bit-nonce cases). That file was last
  changed upstream at commit `e0df04e` (repo HEAD `6d7cccd` as of 2026-06-11).
