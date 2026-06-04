# lean-chacha-poly

Formally verified ChaCha20-Poly1305 AEAD in Lean 4.
A focused, self-contained first verification effort.

## Why this scope

ChaCha20-Poly1305 is the ideal first target because it is:

- **Axiom-free**: no primality assumptions, no external axioms.
  The entire proof chain follows from Lean's standard library.
- **Mathlib-free**: no algebraic geometry, no field theory beyond
  modular arithmetic over a fixed prime. `omega` and `simp` do
  the heavy lifting.
- **Cleanly decomposable**: the two capstone theorems each split
  into sub-goals that are independent and modest in difficulty.
- **Critically important**: ChaCha20-Poly1305 is TLS 1.3's
  preferred cipher suite. A verified implementation is directly
  useful in practice.

## Capstone theorems

### 1. ChaCha20 involution

```lean
theorem chacha20_involutive (key nonce counter msg) :
    chacha20 key nonce counter (chacha20 key nonce counter msg) = msg
```

**Proof chain:**

```
chacha20_involutive
  └── xorBytes_self_cancel          ← THE key lemma (Spec/Xor.lean)
        └── UInt8.xor_cancel        ← (x ^^^ k) ^^^ k = x
  └── keystream_length              ← precondition: lengths match
        └── serializeBlock_length   ← each block = 64 bytes
              └── u32ToLe_length    ← each word → 4 bytes
```

All of these are low-difficulty proofs. `xorBytes_self_cancel`
is a single list induction. `keystream_length` is arithmetic
about ceiling division. `serializeBlock_length` is a `simp`
after unfolding.

### 2. AEAD roundtrip

```lean
theorem decrypt_encrypt (key nonce plaintext aad) :
    decrypt key nonce (encrypt key nonce plaintext aad) aad
    = some plaintext
```

**Proof chain:**

```
decrypt_encrypt
  └── encrypt_length               ← output = pt.length + 16
        └── chacha20_length        ← cipher preserves length
        └── poly1305_length        ← tag = 16 bytes
  └── List.take_append (ct part)
  └── List.drop_append (tag part)
  └── poly1305 determinism         ← same inputs → same tag (rfl)
  └── chacha20_involutive          ← apply ChaCha20 capstone
```

The AEAD roundtrip is essentially "structural assembly" —
it assembles previously proved lemmas. The only creative step
is the length arithmetic to confirm take/drop split correctly.

## Proof difficulty map

| File | Hardest theorem | Difficulty | Primary tactic |
|------|----------------|------------|----------------|
| Spec/Xor.lean | `xorBytes_self_cancel` | Low | `induction`, `simp` |
| Spec/Keystream.lean | `keystream_length` | Low | `omega` |
| Spec/Block.lean | `serializeBlock_length` | Low | `simp` |
| Spec/QuarterRound.lean | `quarterRound_test_vector` | Trivial | `decide` |
| Poly1305/Spec.lean | `accumulate_lt_P` | Low-med | `induction`, `omega` |
| Poly1305/Spec/Accumulate.lean | `accumulate_eq_poly` | Medium | `induction`, `ring` |
| Poly1305/Spec/Blocking.lean | `toBlocks_length` | Low-med | `induction`, `omega` |
| Aead/Spec.lean | `decrypt_encrypt` | Low | assembly |

No theorem in this library requires Mathlib, field theory, or
number theory beyond `omega` and basic `Nat` lemmas.

## What is NOT proved here

**Side-channel resistance.** The proofs guarantee correctness —
same inputs produce same outputs and decrypt undoes encrypt —
but say nothing about timing. Constant-time execution requires
compiler-level guarantees outside Lean's model. This is
explicitly out of scope.

**Security reductions.** "Breaking ChaCha20-Poly1305 implies
solving a hard problem" is a game-based security proof that
requires a probabilistic framework (see VCV-io). Out of scope.

**Nonce uniqueness.** Using the same (key, nonce) pair for two
messages is catastrophic for Poly1305. The library cannot enforce
this; it is a usage constraint. Out of scope.

## Development order

### Phase 0: make it compile

Fill in all function bodies (currently `sorry`d implementations)
until `lake build` succeeds and the test suite (`lake exe test`)
produces correct output for all RFC 8439 vectors.

Suggested order within Phase 0:
1. `u32ToLe` / `leToU32` / `serializeBlock`
2. `doubleRound`, `tenDoubleRounds`, `chacha20Block`
3. `keystream`, `chacha20`
4. `leToNat16`, `extractR`, `extractS`, `toBlocks`
5. `accumulate`, `poly1305`
6. `derivePolyKey`, `encrypt`, `decrypt`

### Phase 1: foundational lemmas

Prove the leaves of the dependency tree first:
- `UInt8.xor_cancel` (likely `decide`)
- `u32ToLe_length` (likely `simp [u32ToLe]`)
- `serializeBlock_length`
- `keystream_length`
- `poly1305_length`
- `accumulate_lt_P`

### Phase 2: ChaCha20 capstone

- `xorBytes_self_cancel`
- `chacha20_length`
- `chacha20_involutive`  ← ChaCha20 done

### Phase 3: Poly1305 properties

- `toBlocks_length`
- `accumulate_eq_poly` (medium difficulty — induction + ring)
- `accumulate_append`

### Phase 4: AEAD capstone

- `encrypt_length`
- `decrypt_encrypt`  ← AEAD done

### Phase 5: ByteArray bridges

- `ChaCha20.Native.chacha20_involutive`
- `Poly1305.Native.poly1305_size`
- `Aead.Native.decrypt_encrypt`

## Exit criteria

The project is complete when:
1. `lake build` succeeds with zero `sorry` warnings
2. `lake exe test` prints all ✓ for RFC 8439 vectors
3. The three capstone theorems compile:
   - `ChaCha20.Spec.chacha20_involutive`
   - `Aead.Spec.decrypt_encrypt`
   - `Aead.Native.decrypt_encrypt`

## File structure

```
lean-chacha-poly/
├── lakefile.lean
├── lean-toolchain         (Lean 4.29.1)
├── PLAN.md
├── LeanChachaPoly.lean    (root import)
├── LeanChachaPoly/
│   ├── ChaCha20/
│   │   ├── Spec.lean              types, definitions, capstones C1–C5
│   │   ├── Native.lean            ByteArray bridge
│   │   └── Spec/
│   │       ├── QuarterRound.lean  QR properties, test vector
│   │       ├── Block.lean         block function size
│   │       ├── Keystream.lean     keystream_length
│   │       └── Xor.lean           xorBytes_self_cancel (KEY LEMMA)
│   ├── Poly1305/
│   │   ├── Spec.lean              types, definitions, capstones P1–P5
│   │   ├── Native.lean            ByteArray bridge
│   │   └── Spec/
│   │       ├── Accumulate.lean    accumulate = polynomial eval
│   │       └── Blocking.lean      toBlocks properties
│   └── Aead/
│       ├── Spec.lean              construction + capstones A1–A5
│       ├── Native.lean            ByteArray bridge
│       └── Spec/
│           ├── KeyDerivation.lean padTo16, le64 lemmas
│           └── MacData.lean       macData structural lemmas
└── Test/
    ├── Main.lean
    ├── Helpers.lean
    ├── ChaCha20Test.lean  RFC 8439 §2.1.1, §2.3.2, §2.4.2, A.1–A.2
    ├── Poly1305Test.lean  RFC 8439 §2.5.2, A.3 #1–7
    └── AeadTest.lean      RFC 8439 §2.6.2, §2.8.2, A.5 + integration
```

## References

- RFC 8439 — ChaCha20 and Poly1305 for IETF Protocols (June 2018)
- D.J. Bernstein, "ChaCha, a variant of Salsa20" (2008)
- D.J. Bernstein, "The Poly1305-AES message-authentication code" (2005)
- kim-em/lean-zip — architectural inspiration
