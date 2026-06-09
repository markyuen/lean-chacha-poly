import LeanChachaPoly.Aead.Spec

/-!
# AEAD Sub-proofs: Key Derivation and MAC Data

Small structural lemmas used in the capstone proof.
-/

namespace Aead.Spec

open ChaCha20.Spec Poly1305.Spec

/-! ## Key derivation -/

/-- The derived Poly1305 key is always 32 bytes (by construction). -/
theorem derivePolyKey_size (key : Key) (nonce : Nonce) :
    (derivePolyKey key nonce).val.length = 32 :=
  (derivePolyKey key nonce).property

/-! ## padTo16 -/

theorem padTo16_length_mod (data : List UInt8) :
    (padTo16 data).val.length % 16 = 0 :=
  (padTo16 data).property

theorem padTo16_prefix (data : List UInt8) :
    (padTo16 data).val.take data.length = data := by
  simp only [padTo16]
  split
  · exact List.take_length
  · exact (List.take_append_of_le_length (Nat.le_refl _)).trans List.take_length

theorem padTo16_length_ge (data : List UInt8) :
    data.length ≤ (padTo16 data).val.length := by
  simp only [padTo16]
  split
  · exact Nat.le_refl _
  · simp only [List.length_append, List.length_replicate]; omega

/-! ## le64 -/

@[simp]
theorem le64_length (n : Nat) : (le64 n).val.length = 8 := (le64 n).property

/-! ## macData structure -/

/-- The underlying bytes of `macData`, for list-level reasoning. -/
theorem macData_val (aad ct : List UInt8) :
    (macData aad ct).val =
      (padTo16 aad).val ++ (padTo16 ct).val ++ (le64 aad.length).val ++ (le64 ct.length).val :=
  rfl

/-- macData length is a multiple of 16 plus 16 (the length fields). -/
theorem macData_length (aad ct : List UInt8) :
    (macData aad ct).val.length =
      (padTo16 aad).val.length + (padTo16 ct).val.length + 16 := by
  simp only [macData_val, List.length_append, le64_length]

/-! ## Tag splitting -/

/-- When `ct` has length `n`, the last 16 bytes of `ct ++ tag` are `tag`,
    given `tag.length = 16`. -/
theorem drop_ct_eq_tag (ct tag : List UInt8) (_ : tag.length = 16) :
    (ct ++ tag).drop ct.length = tag := by
  rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length,
      List.nil_append]

/-- The first `ct.length` bytes of `ct ++ tag` are `ct`. -/
theorem take_ct_eq_ct (ct tag : List UInt8) :
    (ct ++ tag).take ct.length = ct := by
  rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]

end Aead.Spec
