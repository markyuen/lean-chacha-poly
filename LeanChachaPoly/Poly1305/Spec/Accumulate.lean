import LeanChachaPoly.Poly1305.Spec

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

/-- Closed-form polynomial evaluation at point r over GF(P).
    `zipIdx` pairs each block with its index as `(block, i)`. -/
def evalPoly (r : Nat) (blocks : List Nat) : Nat :=
  blocks.zipIdx.foldl (fun acc (m, i) =>
    (acc + m * Nat.pow r (blocks.length - i)) % P) 0

/-! ## The equivalence theorem -/

/-- The iterative accumulation computes the same value as
    the closed-form polynomial evaluation.

    NOTE: still unproved. The original proof relied on `ring_nf`
    (a Mathlib tactic unavailable in this pure-stdlib project) and on
    the removed `List.enum_append` lemma. -/
theorem accumulate_eq_poly (r : Nat) (blocks : List Nat) :
    accumulate r blocks = evalPoly r blocks := by
  sorry -- Algebraic identity: foldl with new block = poly shift

/-! ## Linearity: accumulate is linear in each block -/

/-- Scaling a single block scales the tag proportionally. -/
theorem accumulate_single (r m : Nat) :
    accumulate r [m] = (m * r) % P := by
  simp [accumulate, step]

/-- Prepending a block shifts the polynomial degree: the new (first) block
    `m` is multiplied by the highest power of `r`.

    NOTE: the statement was previously **incorrect** — it gave `m` the power
    `r¹` and `accumulate rest` the power `rⁿ`, but `foldl` processes the head
    first, so `m` actually accrues the *highest* power `r^(rest.length+1)`.
    (Counterexample to the old form: `r=3, m=1, rest=[2]` gives
    `accumulate = 15` but the old RHS evaluated to `21`.)

    Still unproved: needs an "initial-value distribution" lemma
    `bs.foldl (step r) s = (s·r^bs.length + accumulate r bs) % P`, whose proof
    is manual modular arithmetic (`Nat.add_mod`/`Nat.mul_mod`) — `Nat.ModEq`
    is unavailable in this pure-stdlib project. -/
theorem accumulate_cons (r m : Nat) (rest : List Nat) :
    accumulate r (m :: rest) =
      (m * Nat.pow r (rest.length + 1) + accumulate r rest) % P := by
  sorry

end Poly1305.Spec
