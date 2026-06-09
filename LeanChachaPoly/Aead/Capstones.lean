import LeanChachaPoly.Aead.Spec
import LeanChachaPoly.ChaCha20.Capstones

/-!
# AEAD Capstones

The top-level functional guarantees of the AEAD construction, assembled from the
ChaCha20 involution and the Poly1305 tag length:

- `decrypt_encrypt` — the roundtrip: decrypting an encryption returns the plaintext.
- `encrypt_length`, `decrypt_short`, `encrypt_ct_indep_of_aad` — supporting shape facts.

The *authenticity* capstones (`decrypt_verifies`, `macData_inj`) live in
`Aead/Spec/Security.lean`.
-/

namespace Aead.Spec

open ChaCha20.Spec Poly1305.Spec

/-- **Capstone.** The roundtrip — the central correctness theorem of the library:
    `decrypt` of an `encrypt` returns the original plaintext. `encrypt` emits
    `ct ‖ tag`; `decrypt` splits off `ct`, recomputes the same tag (so the check
    passes), and applies `chacha20` again, which is its own inverse. -/
theorem decrypt_encrypt (key : Key) (nonce : Nonce)
    (plaintext aad : List UInt8) :
    decrypt key nonce (encrypt key nonce plaintext aad) aad
    = some plaintext := by
  have htag : (poly1305 (derivePolyKey key nonce)
      (macData aad (chacha20 key nonce 1 plaintext)).val).val.length = 16 :=
    poly1305_length _ _
  unfold encrypt decrypt
  -- The ciphertext+tag is at least 16 bytes, so the length guard fails.
  rw [if_neg (by rw [List.length_append, htag]; omega)]
  -- ctLen = (ct ++ tag).length - 16 = ct.length; take/drop split ct and tag.
  simp only [List.length_append, htag, Nat.add_sub_cancel,
    List.take_append_of_le_length (Nat.le_refl _), List.take_length,
    List.drop_append_of_le_length (Nat.le_refl _), List.drop_length,
    List.nil_append, beq_self_eq_true, if_true]
  -- result = some (chacha20 1 (chacha20 1 plaintext)) = some plaintext.
  rw [chacha20_involutive]

/-- **Supporting.** Ciphertext output length is the plaintext length plus the 16-byte tag. -/
theorem encrypt_length (key : Key) (nonce : Nonce)
    (plaintext aad : List UInt8) :
    (encrypt key nonce plaintext aad).length
    = plaintext.length + 16 := by
  simp [encrypt, List.length_append,
        chacha20_length, poly1305_length]

/-- **Supporting.** Inputs shorter than the 16-byte tag are rejected outright. -/
theorem decrypt_short (key : Key) (nonce : Nonce) (aad : List UInt8)
    (ct : List UInt8) (h : ct.length < 16) :
    decrypt key nonce ct aad = none := by
  simp [decrypt, h]

/-- **Supporting.** AAD is authenticated but not encrypted: the ciphertext bytes do
    not depend on the associated data. -/
theorem encrypt_ct_indep_of_aad (key : Key) (nonce : Nonce)
    (plaintext aad₁ aad₂ : List UInt8) :
    (encrypt key nonce plaintext aad₁).take plaintext.length =
    (encrypt key nonce plaintext aad₂).take plaintext.length := by
  simp only [encrypt]
  have h : (chacha20 key nonce 1 plaintext).length = plaintext.length :=
    chacha20_length key nonce 1 plaintext
  rw [List.take_append_of_le_length (h ▸ Nat.le_refl _),
      List.take_append_of_le_length (h ▸ Nat.le_refl _)]

/-- **Supporting.** The empty-plaintext roundtrip (ciphertext is just the tag). -/
theorem decrypt_encrypt_empty (key : Key) (nonce : Nonce) (aad : List UInt8) :
    decrypt key nonce (encrypt key nonce [] aad) aad = some [] :=
  decrypt_encrypt key nonce [] aad

end Aead.Spec
