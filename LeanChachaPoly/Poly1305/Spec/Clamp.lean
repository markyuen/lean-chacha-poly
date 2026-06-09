import LeanChachaPoly.Poly1305.Spec
import Mathlib

/-!
# Poly1305 Clamp matches RFC 8439 §2.5.1

The spec defines clamping as a single `Nat` mask
(`r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff`). The RFC instead describes it
byte-wise: clear the top 4 bits of bytes 3, 7, 11, 15 and the low 2 bits of
bytes 4, 8, 12. Here we prove the mask realizes exactly those bit-clears, so
the compact definition is faithful to the standard.
-/

namespace Poly1305.Spec

/-- Clamping ANDs `r` with the fixed mask, bit by bit. -/
theorem clamp_testBit (r j : Nat) :
    (clamp r).testBit j
      = (r.testBit j && (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit j) := by
  unfold clamp
  exact Nat.testBit_and r _ j

/-- Any bit the mask clears is clear in `clamp r`, for every `r`. -/
theorem clamp_bit_clear (r j : Nat)
    (hj : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit j = false) :
    (clamp r).testBit j = false := by
  rw [clamp_testBit, hj, Bool.and_false]

/-- **RFC 8439 §2.5.1.** Clamping clears the top 4 bits of bytes 3, 7, 11, 15
    (bit positions 28–31, 60–63, 92–95, 124–127) and the low 2 bits of bytes
    4, 8, 12 (bit positions 32–33, 64–65, 96–97). For every `r`, all 22 of
    these bits vanish in `clamp r`. -/
theorem clamp_rfc (r : Nat) :
    ∀ j ∈ ({28, 29, 30, 31, 60, 61, 62, 63, 92, 93, 94, 95, 124, 125, 126, 127,
            32, 33, 64, 65, 96, 97} : Finset Nat),
      (clamp r).testBit j = false := by
  intro j hj
  fin_cases hj <;> exact clamp_bit_clear r _ (by decide)

end Poly1305.Spec
