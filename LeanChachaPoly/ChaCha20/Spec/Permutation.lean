import LeanChachaPoly.ChaCha20.Spec
import Mathlib

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

/-- **Key lemma.** `quarterRoundInv` undoes `quarterRound'`. (Discharged by
    `bv_decide`, which adds a trusted native SAT-certificate axiom — the library's
    only non-foundational dependency.) -/
theorem quarterRoundInv_quarterRound (p : UInt32 × UInt32 × UInt32 × UInt32) :
    quarterRoundInv (quarterRound' p) = p := by
  obtain ⟨a, b, c, d⟩ := p
  simp only [quarterRound', quarterRound, quarterRoundInv, rotl32, Prod.mk.injEq]
  bv_decide

/-- **Key lemma.** `quarterRound'` undoes `quarterRoundInv` (see the axiom note above). -/
theorem quarterRound_quarterRoundInv (p : UInt32 × UInt32 × UInt32 × UInt32) :
    quarterRound' (quarterRoundInv p) = p := by
  obtain ⟨a, b, c, d⟩ := p
  simp only [quarterRound', quarterRound, quarterRoundInv, rotl32, Prod.mk.injEq]
  bv_decide

/-- **Capstone.** The quarter round is a bijection of `UInt32⁴`, with explicit
    inverse `quarterRoundInv` — the structural reason ChaCha20 is permutation-based. -/
theorem quarterRound_bijective : Function.Bijective quarterRound' :=
  Function.bijective_iff_has_inverse.mpr
    ⟨quarterRoundInv, quarterRoundInv_quarterRound, quarterRound_quarterRoundInv⟩

end ChaCha20.Spec
