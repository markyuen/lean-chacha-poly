import LeanChachaPoly.Fast.ChaCha20
import LeanChachaPoly.Fast.Poly1305

/-!
# ChaCha20-Poly1305 AEAD — fast implementation

The RFC 8439 §2.8 construction assembled from the fast ChaCha20 and
Poly1305, mirroring `Aead.Spec` definition-for-definition so the bridge
proof composes the component bridges.

Equivalence with `Aead.Spec.encrypt`/`Aead.Spec.decrypt` is proved in
`LeanChachaPoly.Fast.Bridge.Aead` (`encrypt_eq_spec` / `decrypt_eq_spec`),
together with the fast-side roundtrip `decrypt_encrypt`.

This file is Mathlib-free; it is linked into the `test` and `bench`
executables.
-/

namespace Aead.Fast

/-! ## Types -/

abbrev Key   := ChaCha20.Fast.Key
abbrev Nonce := ChaCha20.Fast.Nonce

/-! ## Poly1305 one-time key derivation (RFC 8439 §2.6) -/

/-- Run ChaCha20 with counter=0, take the first 32 keystream bytes as the
    Poly1305 key. -/
def derivePolyKey (key : Key) (nonce : Nonce) : Poly1305.Fast.Key :=
  ⟨(ChaCha20.Fast.keystream key nonce 0 64).extract 0 32, by
    rw [ByteArray.size_extract, ChaCha20.Fast.size_keystream]; omega⟩

/-! ## MAC data construction (RFC 8439 §2.8) -/

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate n 0)

/-- Pad a byte array to a multiple of 16 with zeros. -/
def padTo16 (data : ByteArray) : ByteArray :=
  if data.size % 16 = 0 then data
  else data ++ zeros (16 - data.size % 16)

/-- Push a `Nat` as 8 little-endian bytes — the fast `le64`, unrolled. -/
def pushLe64 (acc : ByteArray) (n : Nat) : ByteArray :=
  let byte (i : Nat) : UInt8 := UInt8.ofNat ((n >>> (i * 8)) % 256)
  let acc := (((acc.push (byte 0)).push (byte 1)).push (byte 2)).push (byte 3)
  (((acc.push (byte 4)).push (byte 5)).push (byte 6)).push (byte 7)

/-- The Poly1305 authentication input per RFC 8439 §2.8:
    pad(aad) ‖ pad(ciphertext) ‖ len(aad) as 8-LE ‖ len(ct) as 8-LE. -/
def macData (aad ciphertext : ByteArray) : ByteArray :=
  pushLe64 (pushLe64 (padTo16 aad ++ padTo16 ciphertext) aad.size) ciphertext.size

/-! ## Encrypt and decrypt -/

/-- AEAD encryption: returns ciphertext ‖ 16-byte tag. -/
def encrypt (key : Key) (nonce : Nonce)
    (plaintext aad : ByteArray) : ByteArray :=
  let polyKey    := derivePolyKey key nonce
  let ciphertext := ChaCha20.Fast.chacha20 key nonce 1 plaintext
  let tag        := Poly1305.Fast.poly1305 polyKey (macData aad ciphertext)
  ciphertext ++ tag

/-- AEAD decryption: returns `some plaintext` on success, `none` if the tag
    does not match. Same timing caveat as `Aead.Spec.decrypt`: the tag
    comparison is not constant-time. -/
def decrypt (key : Key) (nonce : Nonce)
    (ciphertextAndTag aad : ByteArray) : Option ByteArray :=
  if ciphertextAndTag.size < 16 then none
  else
    let ctLen      := ciphertextAndTag.size - 16
    let ciphertext := ciphertextAndTag.extract 0 ctLen
    let recvTag    := ciphertextAndTag.extract ctLen ciphertextAndTag.size
    let polyKey    := derivePolyKey key nonce
    let expTag     := Poly1305.Fast.poly1305 polyKey (macData aad ciphertext)
    if recvTag == expTag then
      some (ChaCha20.Fast.chacha20 key nonce 1 ciphertext)
    else none

end Aead.Fast
