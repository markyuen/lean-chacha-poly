import LeanChachaPoly.Fast.Aead
import LeanChachaPoly.Fast.Bridge.ChaCha20
import LeanChachaPoly.Fast.Bridge.Poly1305
import LeanChachaPoly.Aead.Spec.KeyDerivation
import LeanChachaPoly.Aead.Spec.MacData
import LeanChachaPoly.Aead.Correctness

/-!
# Fast bridge — AEAD

Proves the fast `ByteArray` AEAD equal to `Aead.Spec` (capstones
`encrypt_eq_spec` / `decrypt_eq_spec`), composing the ChaCha20 and Poly1305
bridges through the RFC 8439 §2.8 construction, and inherits the fast-side
roundtrip `decrypt_encrypt` from the spec's capstone via injectivity of
`(·.data.toList)`.
-/

namespace Aead.Fast

open Fast.Bridge

/-! ## Key derivation -/

/-- **Supporting.** Fast one-time poly key matches `Spec.derivePolyKey`. -/
theorem derivePolyKey_eq (key : Key) (nonce : Nonce) :
    (derivePolyKey key nonce).toSpec
      = Aead.Spec.derivePolyKey key.toSpec nonce.toSpec := by
  apply Subtype.ext
  simp only [Fast.BytesA.toSpec, derivePolyKey, Aead.Spec.derivePolyKey]
  rw [toList_extract, ChaCha20.Fast.keystream_toList]
  simp
  rfl

/-! ## MAC data -/

/-- **Supporting.** `zeros` is `List.replicate`. -/
theorem zeros_toList (n : Nat) :
    (zeros n).data.toList = List.replicate n 0 := by
  simp [zeros]

/-- **Supporting.** Fast zero-padding matches `Spec.padTo16`. -/
theorem padTo16_toList (b : ByteArray) :
    (padTo16 b).data.toList = (Aead.Spec.padTo16 b.data.toList).val := by
  by_cases h : b.size % 16 = 0
  · rw [padTo16, if_pos h, Aead.Spec.padTo16, dif_pos (by simpa using h)]
  · rw [padTo16, if_neg h, Aead.Spec.padTo16, dif_neg (by simpa using h)]
    simp [zeros_toList]

private theorem range8 : List.range 8 = [0,1,2,3,4,5,6,7] := by decide

/-- **Supporting.** The unrolled length pushes append the spec's `le64`. -/
theorem pushLe64_toList (acc : ByteArray) (n : Nat) :
    (pushLe64 acc n).data.toList = acc.data.toList ++ (Aead.Spec.le64 n).val := by
  simp [pushLe64, Aead.Spec.le64, range8]

/-- **Key lemma.** Fast MAC input matches `Spec.macData`. -/
theorem macData_toList (aad ct : ByteArray) :
    (macData aad ct).data.toList
      = (Aead.Spec.macData aad.data.toList ct.data.toList).val := by
  rw [macData, Aead.Spec.macData_val, pushLe64_toList, pushLe64_toList,
    ByteArray.toList_data_append, padTo16_toList, padTo16_toList]
  simp

/-! ## Constant-time tag comparison -/

/-- **Supporting.** Fast `ctEq` matches `Aead.Spec.ctEq` on the underlying lists. -/
theorem ctEq_toList (a b : ByteArray) :
    Aead.Fast.ctEq a b = Aead.Spec.ctEq a.data.toList b.data.toList := by
  rw [Aead.Fast.ctEq, Aead.Spec.ctEq, length_toList, length_toList,
    ← Array.foldl_toList, Array.toList_zipWith]

/-- **Key lemma.** Fast `ctEq` decides list equality, agreeing with `==` — the
    hinge that lets the constant-time comparison in `Fast.decrypt` bridge to the
    `==` of `Aead.Spec.decrypt`. -/
theorem ctEq_toList_beq (a b : ByteArray) :
    Aead.Fast.ctEq a b = (a.data.toList == b.data.toList) := by
  rw [ctEq_toList, ← Aead.Spec.beq_eq_ctEq]

/-! ## Capstones -/

/-- **Capstone.** Fast AEAD encryption equals the spec on every input. -/
theorem encrypt_eq_spec (key : Key) (nonce : Nonce) (pt aad : ByteArray) :
    (encrypt key nonce pt aad).data.toList
      = Aead.Spec.encrypt key.toSpec nonce.toSpec pt.data.toList aad.data.toList := by
  rw [encrypt, Aead.Spec.encrypt, ByteArray.toList_data_append,
    Poly1305.Fast.poly1305_eq_spec, derivePolyKey_eq, macData_toList,
    ChaCha20.Fast.chacha20_eq_spec]

/-- **Capstone.** Fast AEAD decryption equals the spec on every input
    (including rejecting exactly the same forgeries). -/
theorem decrypt_eq_spec (key : Key) (nonce : Nonce) (ctt aad : ByteArray) :
    (decrypt key nonce ctt aad).map (·.data.toList)
      = Aead.Spec.decrypt key.toSpec nonce.toSpec ctt.data.toList aad.data.toList := by
  have hct : (ctt.extract 0 (ctt.size - 16)).data.toList
      = ctt.data.toList.take (ctt.size - 16) := by
    simp
  rw [decrypt, Aead.Spec.decrypt]
  simp only [length_toList]
  split
  · rfl
  · next hlen =>
    have htag : (ctt.extract (ctt.size - 16) ctt.size).data.toList
        = ctt.data.toList.drop (ctt.size - 16) := by
      rw [toList_extract, List.take_of_length_le (by simp)]
    rw [ctEq_toList_beq, Poly1305.Fast.poly1305_eq_spec, derivePolyKey_eq,
      macData_toList, hct, htag]
    split
    · rw [Option.map_some, ChaCha20.Fast.chacha20_eq_spec, hct]
    · rfl

/-- **Capstone.** Fast-side roundtrip, inherited from the spec's
    `decrypt_encrypt` through the bridges. -/
theorem decrypt_encrypt (key : Key) (nonce : Nonce) (pt aad : ByteArray) :
    decrypt key nonce (encrypt key nonce pt aad) aad = some pt := by
  have h := decrypt_eq_spec key nonce (encrypt key nonce pt aad) aad
  rw [encrypt_eq_spec, Aead.Spec.decrypt_encrypt] at h
  cases hd : decrypt key nonce (encrypt key nonce pt aad) aad with
  | none => rw [hd] at h; simp at h
  | some b =>
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [toList_inj h]

end Aead.Fast
