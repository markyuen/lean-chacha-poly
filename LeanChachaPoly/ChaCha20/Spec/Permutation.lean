import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.ChaCha20.Spec.QuarterRound
import Mathlib.Logic.Function.Basic

/-!
# ChaCha20 Quarter-Round is a Permutation

The quarter round is built only from invertible steps — modular additions
`x := x + y` (undo with `x - y`) and rotate-xors `x := (x ⊕ y) <<< n`
(undo with `x := (x >>> n) ⊕ y`). So it is a bijection of `UInt32⁴`. This is
the structural reason ChaCha20 is a permutation (and hence why the
`add_initial_state` feed-forward is what makes the block function one-way).
-/

namespace ChaCha20.Spec

/-- The quarter round as a map on 4-tuples. -/
def quarterRound' (p : UInt32 × UInt32 × UInt32 × UInt32) :
    UInt32 × UInt32 × UInt32 × UInt32 :=
  quarterRound p.1 p.2.1 p.2.2.1 p.2.2.2

/-- Inverse of the quarter round: undo each step in reverse, rotating by `32 - n`
    to invert a left-rotation by `n`, and subtracting to invert each addition. -/
def quarterRoundInv : UInt32 × UInt32 × UInt32 × UInt32 → UInt32 × UInt32 × UInt32 × UInt32
  | (a, b, c, d) =>
    let b1 := rotl32 b 25 ^^^ c
    let c1 := c - d
    let d1 := rotl32 d 24 ^^^ a
    let a1 := a - b1
    let b0 := rotl32 b1 20 ^^^ c1
    let c0 := c1 - d1
    let d0 := rotl32 d1 16 ^^^ a1
    let a0 := a1 - b0
    (a0, b0, c0, d0)

/-! Each step of the round telescopes through one of three cancellations: a
    rotation undone by its complement (`rotl32_inv`, specialized to the four
    ChaCha amounts below), an XOR undone by repeating its operand
    (`xor_self_cancel`), and a modular add/subtract pair. -/

private theorem rinv7  (X : UInt32) : rotl32 (rotl32 X 7)  25 = X := rotl32_inv 7  X (by decide)
private theorem rinv8  (X : UInt32) : rotl32 (rotl32 X 8)  24 = X := rotl32_inv 8  X (by decide)
private theorem rinv12 (X : UInt32) : rotl32 (rotl32 X 12) 20 = X := rotl32_inv 12 X (by decide)
private theorem rinv16 (X : UInt32) : rotl32 (rotl32 X 16) 16 = X := rotl32_inv 16 X (by decide)
private theorem rinv20 (X : UInt32) : rotl32 (rotl32 X 20) 12 = X := rotl32_inv 20 X (by decide)
private theorem rinv24 (X : UInt32) : rotl32 (rotl32 X 24) 8  = X := rotl32_inv 24 X (by decide)
private theorem rinv25 (X : UInt32) : rotl32 (rotl32 X 25) 7  = X := rotl32_inv 25 X (by decide)

private theorem add_sub_self (a b : UInt32) : a + b - b = a := by
  apply UInt32.toBitVec_inj.1; simp

private theorem sub_add_self (a b : UInt32) : a - b + b = a := by
  apply UInt32.toBitVec_inj.1; simp

/-- **Key lemma.** `quarterRoundInv` undoes `quarterRound'`. -/
theorem quarterRoundInv_quarterRound (p : UInt32 × UInt32 × UInt32 × UInt32) :
    quarterRoundInv (quarterRound' p) = p := by
  obtain ⟨a, b, c, d⟩ := p
  simp only [quarterRound', quarterRound, quarterRoundInv, rinv7, rinv8, rinv12, rinv16,
    xor_self_cancel, add_sub_self]

/-- **Key lemma.** `quarterRound'` undoes `quarterRoundInv`. -/
theorem quarterRound_quarterRoundInv (p : UInt32 × UInt32 × UInt32 × UInt32) :
    quarterRound' (quarterRoundInv p) = p := by
  obtain ⟨a, b, c, d⟩ := p
  simp only [quarterRound', quarterRound, quarterRoundInv, rinv25, rinv24, rinv20, rinv16,
    xor_self_cancel, sub_add_self]

/-- **Capstone.** The quarter round is a bijection of `UInt32⁴`, with explicit
    inverse `quarterRoundInv` — the structural reason ChaCha20 is permutation-based. -/
theorem quarterRound_bijective : Function.Bijective quarterRound' :=
  Function.bijective_iff_has_inverse.mpr
    ⟨quarterRoundInv, quarterRoundInv_quarterRound, quarterRound_quarterRoundInv⟩

end ChaCha20.Spec
