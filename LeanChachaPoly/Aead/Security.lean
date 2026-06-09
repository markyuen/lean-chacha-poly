import LeanChachaPoly.Aead.Spec
import LeanChachaPoly.Aead.Spec.KeyDerivation
import LeanChachaPoly.Aead.Spec.MacData
import Mathlib

/-!
# AEAD Authenticity — structural properties

`decrypt_verifies` is the *verify-before-decrypt* invariant: `decrypt` returns
plaintext only when the received tag matches the tag recomputed over
`(aad, ciphertext)`. There is no control-flow path that releases plaintext on
an authentication failure — the only `some` is guarded by the tag check.

`le64_inj` / `macData_aad_binding`: the RFC 8439 §2.8 length fields make the MAC
input injective in the associated data, so changing the AAD changes the MAC
input (the deterministic core of "reject on AAD mismatch").
-/

namespace Aead.Spec

open ChaCha20.Spec Poly1305.Spec

/-- **Capstone (verify-before-decrypt).** If `decrypt` returns `some _`, then the received
    tag (the last 16 bytes) equals the Poly1305 tag recomputed from the derived
    one-time key over `macData aad ciphertext`. Authentication is checked before
    any plaintext is produced. -/
theorem decrypt_verifies (key : Key) (nonce : Nonce) (ctAndTag aad pt : List UInt8)
    (h : decrypt key nonce ctAndTag aad = some pt) :
    ctAndTag.drop (ctAndTag.length - 16)
      = (poly1305 (derivePolyKey key nonce)
          (macData aad (ctAndTag.take (ctAndTag.length - 16))).val).val := by
  simp only [decrypt] at h
  split at h
  · simp at h
  · split at h
    · rename_i htag
      exact eq_of_beq htag
    · simp at h

/-! ## Length-field injectivity -/

/-- `UInt8.ofNat` is injective on byte values. -/
private theorem ofNat_inj_lt {a b : Nat} (ha : a < 256) (hb : b < 256)
    (h : UInt8.ofNat a = UInt8.ofNat b) : a = b := by
  have := congrArg UInt8.toNat h
  simp only [UInt8.toNat_ofNat'] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact this

/-- **Key lemma.** The 8-byte little-endian length encoding is injective on 64-bit values. -/
theorem le64_inj (n m : Nat) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (h : le64 n = le64 m) : n = m := by
  have hv : (le64 n).val = (le64 m).val := congrArg Subtype.val h
  have key : ∀ i, i < 8 → n / 2 ^ (i * 8) % 256 = m / 2 ^ (i * 8) % 256 := by
    intro i hi
    have hopt : (le64 n).val[i]? = (le64 m).val[i]? := by rw [hv]
    simp only [le64, List.getElem?_map, List.getElem?_range, hi,
      Option.map_some, Option.some.injEq, Nat.shiftRight_eq_div_pow] at hopt
    exact ofNat_inj_lt (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) hopt
  have k0 := key 0 (by norm_num); have k1 := key 1 (by norm_num)
  have k2 := key 2 (by norm_num); have k3 := key 3 (by norm_num)
  have k4 := key 4 (by norm_num); have k5 := key 5 (by norm_num)
  have k6 := key 6 (by norm_num); have k7 := key 7 (by norm_num)
  norm_num at k0 k1 k2 k3 k4 k5 k6 k7
  omega

/-- The MAC input determines the associated data (for a fixed ciphertext): the
    padding plus the `le64` length field recover `aad` exactly. -/
theorem macData_aad_eq (aad₁ aad₂ ct : List UInt8)
    (h1 : aad₁.length < 2 ^ 64) (h2 : aad₂.length < 2 ^ 64)
    (h : macData aad₁ ct = macData aad₂ ct) : aad₁ = aad₂ := by
  have hpad : (padTo16 aad₁).val = (padTo16 aad₂).val := macData_aad_inj aad₁ aad₂ ct h
  have hlen : aad₁.length = aad₂.length := by
    have h' : (macData aad₁ ct).val = (macData aad₂ ct).val := congrArg Subtype.val h
    rw [macData_val, macData_val, hpad] at h'
    exact le64_inj _ _ h1 h2
      (Subtype.ext (List.append_cancel_left (List.append_cancel_right h')))
  calc aad₁ = (padTo16 aad₁).val.take aad₁.length := (padTo16_prefix aad₁).symm
    _ = (padTo16 aad₂).val.take aad₂.length := by rw [hpad, hlen]
    _ = aad₂ := padTo16_prefix aad₂

/-- **Key lemma (AAD binding).** Changing the associated data changes the Poly1305 MAC input
    — the deterministic core of "decrypt rejects on AAD mismatch". -/
theorem macData_aad_binding (aad₁ aad₂ ct : List UInt8)
    (h1 : aad₁.length < 2 ^ 64) (h2 : aad₂.length < 2 ^ 64) (hne : aad₁ ≠ aad₂) :
    macData aad₁ ct ≠ macData aad₂ ct :=
  fun h => hne (macData_aad_eq aad₁ aad₂ ct h1 h2 h)

/-- The MAC input determines the ciphertext (for a fixed AAD). -/
theorem macData_ct_eq (aad ct₁ ct₂ : List UInt8)
    (h1 : ct₁.length < 2 ^ 64) (h2 : ct₂.length < 2 ^ 64)
    (h : macData aad ct₁ = macData aad ct₂) : ct₁ = ct₂ := by
  have hpad : (padTo16 ct₁).val = (padTo16 ct₂).val := macData_ct_inj aad ct₁ ct₂ h
  have hlen : ct₁.length = ct₂.length := by
    have h' : (macData aad ct₁).val = (macData aad ct₂).val := congrArg Subtype.val h
    rw [macData_val, macData_val, hpad] at h'
    exact le64_inj _ _ h1 h2 (Subtype.ext (List.append_cancel_left h'))
  calc ct₁ = (padTo16 ct₁).val.take ct₁.length := (padTo16_prefix ct₁).symm
    _ = (padTo16 ct₂).val.take ct₂.length := by rw [hpad, hlen]
    _ = ct₂ := padTo16_prefix ct₂

/-- **Key lemma (ciphertext binding).** Changing the ciphertext changes the Poly1305 MAC
    input — the deterministic core of "decrypt rejects on a ciphertext change". -/
theorem macData_ct_binding (aad ct₁ ct₂ : List UInt8)
    (h1 : ct₁.length < 2 ^ 64) (h2 : ct₂.length < 2 ^ 64) (hne : ct₁ ≠ ct₂) :
    macData aad ct₁ ≠ macData aad ct₂ :=
  fun h => hne (macData_ct_eq aad ct₁ ct₂ h1 h2 h)

/-! ## Full MAC-input injectivity -/

/-- `padTo16` length depends only on the input length. -/
private theorem padTo16_length_eq {a b : List UInt8} (hl : a.length = b.length) :
    (padTo16 a).val.length = (padTo16 b).val.length := by
  have formula : ∀ l : List UInt8, (padTo16 l).val.length =
      if l.length % 16 = 0 then l.length else l.length + (16 - l.length % 16) := by
    intro l; simp only [padTo16]; split
    · rfl
    · simp [List.length_append, List.length_replicate]
  rw [formula, formula, hl]

/-- **Capstone.** The MAC input determines both the AAD and the ciphertext. Distinct
    `(aad, ct)` pairs always produce distinct Poly1305 inputs — the full
    structural authenticity guarantee `macData` provides. -/
theorem macData_inj (aad₁ ct₁ aad₂ ct₂ : List UInt8)
    (ha1 : aad₁.length < 2 ^ 64) (hc1 : ct₁.length < 2 ^ 64)
    (ha2 : aad₂.length < 2 ^ 64) (hc2 : ct₂.length < 2 ^ 64)
    (h : macData aad₁ ct₁ = macData aad₂ ct₂) : aad₁ = aad₂ ∧ ct₁ = ct₂ := by
  have hv : (macData aad₁ ct₁).val = (macData aad₂ ct₂).val := congrArg Subtype.val h
  have htot := congrArg List.length hv
  rw [macData_length, macData_length] at htot
  rw [macData_val, macData_val] at hv
  -- peel the rightmost `le64 |ct|` (length 8) — recovers the ciphertext length
  obtain ⟨hA, hct64⟩ := List.append_inj hv (by
    simp only [List.length_append, le64_length]; omega)
  have hctlen : ct₁.length = ct₂.length := le64_inj _ _ hc1 hc2 (Subtype.ext hct64)
  -- peel the next `le64 |aad|` (length 8) — recovers the AAD length
  obtain ⟨hB, haad64⟩ := List.append_inj hA (by
    simp only [List.length_append]; omega)
  have haadlen : aad₁.length = aad₂.length := le64_inj _ _ ha1 ha2 (Subtype.ext haad64)
  -- now split `padTo16 aad ++ padTo16 ct` using the recovered AAD length
  obtain ⟨hpadA, hpadC⟩ := List.append_inj hB (padTo16_length_eq haadlen)
  refine ⟨?_, ?_⟩
  · calc aad₁ = (padTo16 aad₁).val.take aad₁.length := (padTo16_prefix aad₁).symm
      _ = (padTo16 aad₂).val.take aad₂.length := by rw [hpadA, haadlen]
      _ = aad₂ := padTo16_prefix aad₂
  · calc ct₁ = (padTo16 ct₁).val.take ct₁.length := (padTo16_prefix ct₁).symm
      _ = (padTo16 ct₂).val.take ct₂.length := by rw [hpadC, hctlen]
      _ = ct₂ := padTo16_prefix ct₂

end Aead.Spec
