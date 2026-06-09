import LeanChachaPoly.Poly1305.Spec
import Mathlib

/-!
# Poly1305 Accumulation = Polynomial Evaluation

Proves that the iterative accumulation loop computes the same
value as the closed-form polynomial definition.

## The theorem

`accumulate r [m₁, m₂, ..., mₙ] = (m₁·rⁿ + m₂·rⁿ⁻¹ + ... + mₙ·r) mod P`

In other words, the left fold with `step r` evaluates the polynomial
whose coefficients are the message blocks, at point `r`, over GF(P).

## Why this matters

The spec could have been written either way. We chose the iterative
form (`foldl`) because it's efficient and easy to implement. The
polynomial form is the mathematical definition that matches the
security analysis. Proving they're equal validates that our spec
implements what the cryptographic literature says.

## Proof strategy

Induction on the block list:
- Base: `accumulate r [] = 0 = empty sum`
- Step: `accumulate r (blocks ++ [b]) = ...`
  Unfold one step, apply the induction hypothesis, factor.
-/

namespace Poly1305.Spec

/-! ## Polynomial evaluation -/

/-- Closed-form polynomial evaluation at point `r` over GF(P).

    For blocks `[m₀, …, mₙ₋₁]` this is `(Σⱼ mⱼ · r^(n−j)) mod P`, the polynomial
    whose coefficients are the blocks. We index over `blocks.reverse` so the
    exponent is `k+1` (the position from the end) — this avoids `Nat`
    subtraction and makes the cons-recurrence clean. -/
def evalPoly (r : Nat) (blocks : List Nat) : Nat :=
  (blocks.reverse.zipIdx.map (fun p => p.1 * r ^ (p.2 + 1))).sum % P

/-! ## Initial-value distribution

    Folding `step r` from an arbitrary start `s` distributes as
    `s·r^len + accumulate` — the key lemma behind both the cons-recurrence
    and the polynomial equivalence. Stated as a congruence mod P so the
    empty case is `s ≡ s` with no side condition. -/
/-- **Supporting.** Folding `step r` from an arbitrary start `s` distributes. -/
theorem accumulate_init (r : Nat) (bs : List Nat) (s : Nat) :
    bs.foldl (step r) s ≡ s * r ^ bs.length + accumulate r bs [MOD P] := by
  induction bs generalizing s with
  | nil => simp [accumulate, Nat.ModEq.refl]
  | cons b bs ih =>
    rw [List.foldl_cons]
    have hacc : accumulate r (b :: bs) = bs.foldl (step r) (step r 0 b) := by simp [accumulate]
    rw [List.length_cons, hacc]
    calc bs.foldl (step r) (step r s b)
        ≡ step r s b * r ^ bs.length + accumulate r bs [MOD P] := ih _
      _ ≡ (s + b) * r * r ^ bs.length + accumulate r bs [MOD P] :=
            ((Nat.mod_modEq _ _).mul_right _).add_right _
      _ = s * r ^ (bs.length + 1) + ((b * r) * r ^ bs.length + accumulate r bs) := by ring
      _ ≡ s * r ^ (bs.length + 1) + (step r 0 b * r ^ bs.length + accumulate r bs) [MOD P] := by
            have : (b * r) ≡ step r 0 b [MOD P] := by
              simp only [step, Nat.zero_add]; exact (Nat.mod_modEq _ _).symm
            exact (((this.mul_right _).add_right _).add_left _)
      _ ≡ s * r ^ (bs.length + 1) + bs.foldl (step r) (step r 0 b) [MOD P] :=
            ((ih _).symm.add_left _)

/-- **Supporting.** Prepending a block shifts the polynomial degree: the new (first)
    block `m` is multiplied by the *highest* power of `r`, namely `r^(rest.length+1)`
    (`foldl` processes the head first, so it accrues the highest power). -/
theorem accumulate_cons (r m : Nat) (rest : List Nat) :
    accumulate r (m :: rest) =
      (m * Nat.pow r (rest.length + 1) + accumulate r rest) % P := by
  have h1 : accumulate r (m :: rest) ≡ m * r ^ (rest.length + 1) + accumulate r rest [MOD P] := by
    have e : accumulate r (m :: rest) = rest.foldl (step r) (step r 0 m) := by simp [accumulate]
    rw [e]
    calc rest.foldl (step r) (step r 0 m)
        ≡ step r 0 m * r ^ rest.length + accumulate r rest [MOD P] := accumulate_init r rest _
      _ ≡ (m * r) * r ^ rest.length + accumulate r rest [MOD P] := by
            have : step r 0 m ≡ m * r [MOD P] := by
              simp only [step, Nat.zero_add]; exact Nat.mod_modEq _ _
            exact (this.mul_right _).add_right _
      _ = m * r ^ (rest.length + 1) + accumulate r rest := by ring
  rw [← Nat.mod_eq_of_lt (accumulate_lt_P r (m :: rest))]
  exact h1

/-! ## The equivalence theorem -/

/-- **Key lemma.** The iterative accumulation computes the same value as the
    closed-form polynomial evaluation: Poly1305's fold *is* polynomial evaluation in
    GF(P). This is the property the security analysis reasons about. -/
theorem accumulate_eq_poly (r : Nat) (blocks : List Nat) :
    accumulate r blocks = evalPoly r blocks := by
  induction blocks with
  | nil => simp [accumulate, evalPoly]
  | cons m rest ih =>
    rw [accumulate_cons, ih]
    unfold evalPoly
    rw [List.reverse_cons, List.zipIdx_append, List.map_append, List.sum_append]
    simp only [List.length_reverse, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.pow_eq, Nat.zero_add]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_comm]

/-! ## Linearity: accumulate is linear in each block -/

/-- **Supporting.** A single-block accumulation is just `(m·r) mod P`. -/
theorem accumulate_single (r m : Nat) :
    accumulate r [m] = (m * r) % P := by
  simp [accumulate, step]

end Poly1305.Spec
