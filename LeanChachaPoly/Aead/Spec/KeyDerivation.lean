import LeanChachaPoly.Aead.Spec

/-!
# AEAD Sub-proofs: Key Derivation and MAC Data

Small structural lemmas used in the capstone proof.
-/

namespace Aead.Spec

open ChaCha20.Spec Poly1305.Spec

/-! ## padTo16 -/

/-- **Supporting.** The padded bytes begin with the original data, so `padTo16` is
    undone by `take`-ing the original length. -/
theorem padTo16_prefix (data : List UInt8) :
    (padTo16 data).val.take data.length = data := by
  simp only [padTo16]
  split
  · exact List.take_length
  · exact (List.take_append_of_le_length (Nat.le_refl _)).trans List.take_length

/-! ## le64 -/

@[simp]
theorem le64_length (n : Nat) : (le64 n).val.length = 8 := (le64 n).property

/-! ## macData structure -/

/-- The underlying bytes of `macData`, for list-level reasoning. -/
theorem macData_val (aad ct : List UInt8) :
    (macData aad ct).val =
      (padTo16 aad).val ++ (padTo16 ct).val ++ (le64 aad.length).val ++ (le64 ct.length).val :=
  rfl

/-- **Supporting.** macData length is a multiple of 16 plus 16 (the length fields). -/
theorem macData_length (aad ct : List UInt8) :
    (macData aad ct).val.length =
      (padTo16 aad).val.length + (padTo16 ct).val.length + 16 := by
  simp only [macData_val, List.length_append, le64_length]

end Aead.Spec
