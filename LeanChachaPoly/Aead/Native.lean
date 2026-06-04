import LeanChachaPoly.Aead.Spec
import LeanChachaPoly.ChaCha20.Native
import LeanChachaPoly.Poly1305.Native

/-!
# AEAD Native — ByteArray Bridge
-/

namespace Aead.Native

open Aead.Spec

def encrypt (key : Key) (nonce : Nonce)
    (plaintext aad : ByteArray) : ByteArray :=
  ByteArray.mk (Aead.Spec.encrypt key nonce
    plaintext.data.toList aad.data.toList).toArray

def decrypt (key : Key) (nonce : Nonce)
    (ciphertextAndTag aad : ByteArray) : Option ByteArray :=
  (Aead.Spec.decrypt key nonce
    ciphertextAndTag.data.toList aad.data.toList).map
    (fun bs => ByteArray.mk bs.toArray)

/-! ## Bridge theorems -/

theorem encrypt_eq_spec (key : Key) (nonce : Nonce)
    (plaintext aad : ByteArray) :
    (encrypt key nonce plaintext aad).data.toList =
      Aead.Spec.encrypt key nonce
        plaintext.data.toList aad.data.toList := by
  simp [encrypt, Array.toList_toArray]

/-! ## Derived capstone -/

theorem decrypt_encrypt (key : Key) (nonce : Nonce)
    (plaintext aad : ByteArray) :
    decrypt key nonce (encrypt key nonce plaintext aad) aad
    = some plaintext := by
  simp [decrypt, encrypt_eq_spec]
  rw [Aead.Spec.decrypt_encrypt]
  simp [Option.map, ByteArray.ext_iff, Array.toList_toArray]

end Aead.Native
