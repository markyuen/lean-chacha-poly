import LeanChachaPoly.ChaCha20.Spec
import Std.Tactic.BVDecide

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
-/

namespace ChaCha20.Spec

open ChaCha20.Spec

/-! ## Rotation lemmas

    The individual ARX steps are invertible (rotate-by-`n` is undone by
    rotate-by-`32-n`, and rotation distributes over XOR). These document why the
    quarter round is a permutation; an *algebraic* bijection proof built from them
    (avoiding `bv_decide`) is noted as future work. -/

/-- **Supporting.** `rotl32` by `n` then by `(32-n)` is the identity. -/
theorem rotl32_inv (n : UInt32) (x : UInt32) (_hn : n.toNat < 32) :
    rotl32 (rotl32 x n) (32 - n) = x := by
  unfold rotl32; bv_decide

/-- **Supporting.** `rotl32` distributes over XOR. -/
theorem rotl32_xor (n : UInt32) (x y : UInt32) :
    rotl32 (x ^^^ y) n = (rotl32 x n) ^^^ (rotl32 y n) := by
  unfold rotl32; bv_decide

/-! ## XOR cancellation -/

/-- **Supporting.** XOR with the same value twice is the identity. -/
@[simp]
theorem xor_self_cancel (x y : UInt32) : (x ^^^ y) ^^^ y = x := by
  simp [UInt32.xor_assoc, UInt32.xor_self]

-- The RFC 8439 §2.1.1 quarter-round test vector (and the §2.3.2 block-function
-- vector) are checked at runtime in `Tests/ChaCha20Test.lean`.

end ChaCha20.Spec
