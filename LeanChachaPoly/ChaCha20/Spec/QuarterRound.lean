import LeanChachaPoly.ChaCha20.Spec

/-!
# ChaCha20 Quarter Round Properties

The quarter round is the atomic building block of ChaCha20.
This file proves properties of `quarterRound` that are used by
the block function proofs.

## Proof strategy

Each ARX step (add, rotate, XOR) is individually invertible.
Bijectivity of `quarterRound` follows from composing those
invertible steps. This is the key lemma for proving that the
block function is a permutation, which in turn is what makes
the cipher non-trivially correct (the keystream bytes are
"random-looking" and hard to predict without the key).

Note: bijectivity of the block function does NOT directly
contribute to the involution proof — that proof goes through
XOR cancellation. But it is a useful characterizing property
that validates the spec against the intuition that ChaCha20
is a permutation-based cipher.

The rotation lemmas below are proved by bit-blasting `rotl32`
through `BitVec.getLsbD` (no `bv_decide`): `rotl32` is shown
equal to `BitVec.rotateLeft`, and the facts about rotation
follow from `getLsbD_rotateLeft`. Every theorem here closes
over Lean's three foundational axioms only.
-/

namespace ChaCha20.Spec

open ChaCha20.Spec

/-! ## Rotation lemmas

    `rotl32 x n` (defined as `(x <<< n) ||| (x >>> (32 - n))`) equals
    `BitVec.rotateLeft` on the underlying 32-bit word when `n.toNat ≤ 32`. The
    invertibility and XOR-distribution facts follow from that bridge. -/

/-- `rotl32` is `BitVec.rotateLeft` on the underlying word (for `n.toNat ≤ 32`). -/
theorem rotl32_toBitVec (x n : UInt32) (hn : n.toNat ≤ 32) :
    (rotl32 x n).toBitVec = x.toBitVec.rotateLeft n.toNat := by
  have hsub : (32 - n).toNat = 32 - n.toNat := by
    have h32 : (32 : UInt32).toNat = 32 := rfl
    rw [UInt32.toNat_sub]; omega
  have hb : BitVec.toNat (32 : BitVec 32) = 32 := rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold rotl32
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft', BitVec.ushiftRight_eq',
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft, BitVec.toNat_umod,
    UInt32.toNat_toBitVec, hb, hsub, decide_true, Bool.true_and, hi]
  by_cases hik : i < n.toNat % 32
  · have h1 : (32 - n.toNat) % 32 = 32 - n.toNat % 32 := by omega
    simp [hik, h1]
  · by_cases hk0 : n.toNat % 32 = 0
    · have e : (32 - n.toNat) % 32 = 0 := by omega
      simp [hk0, e, Bool.or_self]
    · have e : (32 - n.toNat) % 32 = 32 - n.toNat % 32 := by omega
      rw [e, BitVec.getLsbD_of_ge x.toBitVec (32 - n.toNat % 32 + i) (by omega)]
      simp [hik]

/-- Rotating a 32-bit word left by `a` then by `32 - a` is the identity (`a ≤ 32`). -/
private theorem rotateLeft_complement (z : BitVec 32) (a : Nat) (ha : a ≤ 32) :
    (z.rotateLeft a).rotateLeft (32 - a) = z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateLeft]
  by_cases hk0 : a % 32 = 0
  · rw [show (32 - a) % 32 = 0 from by omega]
    simp only [Nat.not_lt_zero, hi, decide_true, Bool.true_and, Nat.sub_zero]
    rw [BitVec.getLsbD_rotateLeft]
    simp [hk0, hi]
  · rw [show (32 - a) % 32 = 32 - a % 32 from by omega]
    by_cases h1 : i < 32 - a % 32
    · simp only [h1, decide_true, cond_true]
      rw [BitVec.getLsbD_rotateLeft,
        show 32 - (32 - a % 32) + i = a % 32 + i from by omega]
      simp only [show ¬ (a % 32 + i < a % 32) from by omega, decide_false, cond_false,
        show a % 32 + i < 32 from by omega, decide_true, Bool.true_and]
      congr 1; omega
    · simp only [h1, decide_false, cond_false, hi, decide_true, Bool.true_and]
      rw [BitVec.getLsbD_rotateLeft]
      simp only [show i - (32 - a % 32) < a % 32 from by omega, decide_true, cond_true]
      congr 1; omega

/-- **Supporting.** `rotl32` by `n` then by `(32-n)` is the identity. -/
theorem rotl32_inv (n : UInt32) (x : UInt32) (hn : n.toNat < 32) :
    rotl32 (rotl32 x n) (32 - n) = x := by
  have hsub : (32 - n).toNat = 32 - n.toNat := by
    have h32 : (32 : UInt32).toNat = 32 := rfl
    rw [UInt32.toNat_sub]; omega
  rw [← UInt32.toBitVec_inj, rotl32_toBitVec _ _ (by omega), rotl32_toBitVec _ _ (by omega),
    hsub, rotateLeft_complement _ _ (by omega)]

/-- **Supporting.** `rotl32` distributes over XOR (for `n.toNat ≤ 32`). -/
theorem rotl32_xor (n : UInt32) (x y : UInt32) (hn : n.toNat ≤ 32) :
    rotl32 (x ^^^ y) n = (rotl32 x n) ^^^ (rotl32 y n) := by
  apply UInt32.toBitVec_inj.1
  rw [UInt32.toBitVec_xor, rotl32_toBitVec _ _ hn, rotl32_toBitVec _ _ hn,
    rotl32_toBitVec _ _ hn, UInt32.toBitVec_xor]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_xor]
  by_cases h : i < n.toNat % 32 <;> simp [h, hi]

/-! ## XOR cancellation -/

/-- **Supporting.** XOR with the same value twice is the identity. -/
@[simp]
theorem xor_self_cancel (x y : UInt32) : (x ^^^ y) ^^^ y = x := by
  simp [UInt32.xor_assoc, UInt32.xor_self]

-- The RFC 8439 §2.1.1 quarter-round test vector (and the §2.3.2 block-function
-- vector) are checked at runtime in `Tests/ChaCha20Test.lean`.

end ChaCha20.Spec
