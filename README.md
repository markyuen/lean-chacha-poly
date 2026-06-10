# lean-chacha-poly

A machine-checked **Lean 4** verification of RFC 8439 **ChaCha20-Poly1305 AEAD** —
the AEAD cipher suite preferred by TLS 1.3, WireGuard, and SSH.

It verifies two things most formalizations stop short of combining:

1. **Functional correctness** — the spec computes the right bytes (matches the RFC
   test vectors) and `decrypt ∘ encrypt = id`.
2. **Information-theoretic security** — Poly1305 is an almost-universal hash, giving a
   concrete, *unconditional* forgery bound; this is a real cryptographic theorem, not
   just a "the code does what the pseudocode says" check.

Everything is `sorry`-free and rests on Lean/Mathlib's three foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`) — with a single, explicitly documented
exception (the `bv_decide` SAT-certificate axiom behind the quarter-round bijection).

```
lake exe cache get      # fetch the matching Mathlib build
lake build              # check every proof  (0 sorry)
lake exe test           # run the RFC 8439 vectors + property checks
```

Lean toolchain `v4.29.1`, Mathlib pinned to match.

## Capstone results

### Poly1305 — security (the headline)

| Theorem | File | Statement |
|---|---|---|
| `poly1305_byte_forgery` | `Poly1305/Security` | The real byte-level bound: a forger targeting a fixed tag offset succeeds for at most **`8·⌈L/16⌉`** keys — the famous Poly1305 factor. |
| `poly1305_almost_universal` | `Poly1305/Security` | Almost-universal hashing over the field `ZMod P`: two distinct block-lists collide for at most `max #blocks` keys `r` (root-counting on a nonzero difference polynomial). |
| `toBlocks_inj` / `poly1305_almost_universal_msg'` | `Poly1305/Injectivity` | The `2^(8·len)` padding makes the message→block encoding injective, lifting the bound from block-lists to **distinct messages**. |
| `accumulate_eq_poly` | `Poly1305/Spec/Accumulate` | The iterative MAC loop **is** polynomial evaluation in `GF(2¹³⁰−5)` — the bridge the whole security argument rests on. |
| `poly1305_value` | `Poly1305/Spec/Tag` | The 16-byte tag reads back as exactly `(accumulate + s) mod 2¹²⁸` (serialization is faithful, not lossy). |

### ChaCha20 — correctness & structure

| Theorem | File | Statement |
|---|---|---|
| `chacha20_involutive` | `ChaCha20/Correctness` | Encrypting twice returns the message — encrypt = decrypt for a XOR stream cipher. |
| `quarterRound_bijective` | `ChaCha20/Spec/Permutation` | The quarter round is a bijection of `UInt32⁴` (with explicit inverse) — why ChaCha20 is permutation-based. |
| `keystream_counter_shift` | `ChaCha20/Spec/Seek` | CTR seekability: the keystream is random-access by 64-byte block. |

### AEAD — correctness & authenticity

| Theorem | File | Statement |
|---|---|---|
| `decrypt_encrypt` | `Aead/Correctness` | The roundtrip: `decrypt (encrypt pt aad) aad = some pt`. |
| `decrypt_verifies` | `Aead/Security` | Verify-before-decrypt: plaintext is released only when the recomputed Poly1305 tag matches — there is no path that leaks plaintext on an authentication failure. |
| `macData_inj` (+ `macData_aad_binding`, `macData_ct_binding`) | `Aead/Security` | The RFC §2.8 length-framed MAC input is injective in `(aad, ciphertext)`, so any change to either changes the authenticated input. |

Each primitive also has a **`Native`** module proving the executable `ByteArray`
implementation equals the `List UInt8` spec (`chacha20_eq_spec`, `poly1305_eq_spec`,
`encrypt_eq_spec`/`decrypt_eq_spec`), so every spec theorem transfers to runnable code.

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
    Correctness.lean         chacha20_involutive / chacha20_length      ← capstone
    Native.lean              ByteArray bridge
    Spec/{QuarterRound, Keystream, Seek, Permutation, Xor}.lean
  Poly1305/
    Spec.lean                definitions + basic properties
    Security.lean            almost-universal / byte-level forgery bound ← capstone
    Injectivity.lean         block-encoding injectivity → toBlocks_inj   ← capstone
    Native.lean              ByteArray bridge
    Spec/{Sum, Blocking, Accumulate, Tag, Clamp}.lean
  Aead/
    Spec.lean                construction (encrypt / decrypt)
    Correctness.lean         decrypt_encrypt (the roundtrip)             ← capstone
    Security.lean            verify-before-decrypt, macData injectivity  ← capstone
    Native.lean              ByteArray bridge
    Spec/{KeyDerivation, MacData}.lean
Tests/                       RFC 8439 vectors + property checks
```

Every theorem's doc-comment is tagged `**Capstone.**`, `**Key lemma.**`, or
`**Supporting.**` so its importance is visible at a glance.

## What is NOT covered (and why)

This project proves what is *provable in Lean about the algorithm*. It deliberately does
**not** claim the following:

- **ChaCha20 confidentiality / PRF security.** "The keystream is indistinguishable from
  random" is a *computational* assumption requiring a probabilistic game framework
  (adversaries, advantage, reductions). It is not a theorem one can prove in plain Lean
  about the function — it is out of scope by nature. What *is* proved is the structural
  fact (`quarterRound_bijective`) that ChaCha20 is permutation-based.

- **Primality of `P = 2¹³⁰ − 5`.** The field-level forgery bounds need `ZMod P` to be a
  field, i.e. `P` prime. That 40-digit primality is *assumed* as a hypothesis
  `[Fact (Nat.Prime P)]`, not discharged (it needs a Pratt certificate). The security
  theorems are therefore conditional on this standard, well-known fact.

- **One trusted axiom.** `quarterRound_bijective` (and its two round-trips) are proved by
  `bv_decide`, which validates a SAT/LRAT certificate via the native compiler — the same
  trust tier as `native_decide`. This is the library's *only* non-foundational axiom;
  everything else is axiom-clean. An algebraic reproof (from the rotate/XOR invertibility
  lemmas already present) would remove it — see future work.

- **The clamped key distribution.** The forgery bound is proved over the *full* field
  `ZMod P`. Poly1305 clamps `r`, restricting it to a ~2¹⁰⁶ subset; the bound still holds
  on a subset, but the exact clamped ε-probability (`8⌈L/16⌉ / 2¹⁰⁶`) is not formalized —
  the combinatorial bound is, the probability packaging is presentational.

- **Constant-time / side-channel resistance.** The proofs are about input→output values;
  they say nothing about timing, caches, or power. Constant-time execution is a
  compiler/hardware property outside Lean's evaluation model.

- **Nonce-reuse safety.** Reusing a `(key, nonce)` pair is catastrophic for Poly1305.
  This is a *usage* constraint the types cannot enforce; the library proves correctness
  *given* a fresh nonce.

- **The runtime below the bridge.** The `Native` modules prove the `ByteArray`
  implementation equals the spec; the Lean compiler and runtime that then execute it are
  trusted (as they are for any verified-then-compiled program).

## Future work

- Reprove `quarterRoundInv_quarterRound` / `quarterRound_quarterRoundInv` algebraically
  (via `rotl32_inv` / `rotl32_xor` / `xor_self_cancel`) to make the whole library
  uniformly foundational — no `bv_decide` axiom.
- Discharge `Nat.Prime (2¹³⁰ − 5)` (Pratt certificate) to make the security bounds
  unconditional.
- Package the field bound as the explicit clamped probability `8⌈L/16⌉ / 2¹⁰⁶`.

## References

- RFC 8439 — *ChaCha20 and Poly1305 for IETF Protocols* (June 2018)
- D. J. Bernstein, *ChaCha, a variant of Salsa20* (2008)
- D. J. Bernstein, *The Poly1305-AES message-authentication code* (2005)
- [primefactor-io/xchacha20-poly1305](https://github.com/primefactor-io/xchacha20-poly1305)
  — the Go implementation whose test suite the RFC 8439 vectors in `Tests/` are ported
  1:1 from.
