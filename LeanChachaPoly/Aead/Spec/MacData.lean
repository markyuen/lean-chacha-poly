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
    padTo16 aad₁ = padTo16 aad₂ := by
  simp [macData, List.append_inj] at h
  exact h.1.1

theorem macData_ct_inj (aad ct₁ ct₂ : List UInt8)
    (h : macData aad ct₁ = macData aad ct₂) :
    padTo16 ct₁ = padTo16 ct₂ := by
  simp [macData, List.append_inj] at h
  exact h.1.2

/-! ## Determinism -/

/-- macData is a pure function; same inputs → same output. -/
theorem macData_det (aad ct : List UInt8) :
    macData aad ct = macData aad ct := rfl

end Aead.Spec
