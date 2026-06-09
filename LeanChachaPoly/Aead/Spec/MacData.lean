import LeanChachaPoly.Aead.Spec
import LeanChachaPoly.Aead.Spec.KeyDerivation

/-!
# AEAD MAC Data Properties

Properties of `macData` used to support the authenticate-then-
encrypt / verify-then-decrypt structure.
-/

namespace Aead.Spec

open ChaCha20.Spec Poly1305.Spec

/-! ## macData injectivity

    Two different (aad, ciphertext) pairs produce different macData
    inputs to Poly1305. This is important for security analysis,
    though not needed for the correctness roundtrip proof. -/
theorem macData_aad_inj (aad₁ aad₂ ct : List UInt8)
    (h : macData aad₁ ct = macData aad₂ ct) :
    (padTo16 aad₁).val = (padTo16 aad₂).val := by
  have hv : (macData aad₁ ct).val = (macData aad₂ ct).val := congrArg Subtype.val h
  -- Equal total length forces |padTo16 aad₁| = |padTo16 aad₂|.
  have hlen : (padTo16 aad₁).val.length = (padTo16 aad₂).val.length := by
    have hl := congrArg List.length hv
    rw [macData_length, macData_length] at hl; omega
  -- Reassociate so `padTo16 aad` is the leftmost prefix, then split.
  rw [macData_val, macData_val] at hv
  simp only [List.append_assoc] at hv
  exact List.append_inj_left hv hlen

theorem macData_ct_inj (aad ct₁ ct₂ : List UInt8)
    (h : macData aad ct₁ = macData aad ct₂) :
    (padTo16 ct₁).val = (padTo16 ct₂).val := by
  have hv : (macData aad ct₁).val = (macData aad ct₂).val := congrArg Subtype.val h
  have hlen : (padTo16 ct₁).val.length = (padTo16 ct₂).val.length := by
    have hl := congrArg List.length hv
    rw [macData_length, macData_length] at hl; omega
  -- Strip the common `padTo16 aad` prefix, then split the tail.
  rw [macData_val, macData_val] at hv
  simp only [List.append_assoc] at hv
  replace hv := List.append_cancel_left hv
  exact List.append_inj_left hv hlen

end Aead.Spec
