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
    (derivePolyKey key nonce).bytes.length = 32 :=
  (derivePolyKey key nonce).size

/-! ## padTo16 -/

theorem padTo16_length_mod (data : List UInt8) :
    (padTo16 data).length % 16 = 0 := by
  simp only [padTo16]
  split
  · omega
  · simp only [List.length_append, List.length_replicate]; omega

theorem padTo16_prefix (data : List UInt8) :
    (padTo16 data).take data.length = data := by
  simp only [padTo16]
  split
  · exact List.take_length
  · exact (List.take_append_of_le_length (Nat.le_refl _)).trans List.take_length

theorem padTo16_length_ge (data : List UInt8) :
    data.length ≤ (padTo16 data).length := by
  simp only [padTo16]
  split
  · exact Nat.le_refl _
  · simp only [List.length_append, List.length_replicate]; omega

/-! ## le64 -/

@[simp]
theorem le64_length (n : Nat) : (le64 n).length = 8 := by
  simp [le64]

/-! ## macData structure -/

/-- macData length is a multiple of 16 plus 16 (the length fields). -/
theorem macData_length (aad ct : List UInt8) :
    (macData aad ct).length =
      (padTo16 aad).length + (padTo16 ct).length + 16 := by
  simp only [macData, List.length_append, le64_length]

/-! ## Tag splitting -/

/-- When `ct` has length `n`, the last 16 bytes of `ct ++ tag` are `tag`,
    given `tag.length = 16`. -/
theorem drop_ct_eq_tag (ct tag : List UInt8) (htag : tag.length = 16) :
    (ct ++ tag).drop ct.length = tag := by
  rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length,
      List.nil_append]

/-- The first `ct.length` bytes of `ct ++ tag` are `ct`. -/
theorem take_ct_eq_ct (ct tag : List UInt8) :
    (ct ++ tag).take ct.length = ct := by
  rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]

end Aead.Spec
