import Mathlib.Tactic.Ring

/-!
# Shared summation helper

`foldl_add_eq_sum` turns a left fold that accumulates `acc + g i` into the running
sum `init + (l.map g).sum`. Several Poly1305 proofs reduce a positional byte fold to a
`Finset`/`List` sum this way, so it lives here once rather than being copied per file.
-/

namespace Poly1305.Spec

/-- **Supporting.** Folding `(acc + g i)` over a list is the running sum. -/
theorem foldl_add_eq_sum {α : Type*} (l : List α) (g : α → Nat) (init : Nat) :
    l.foldl (fun acc i => acc + g i) init = init + (l.map g).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih => simp [ih]; ring

end Poly1305.Spec
