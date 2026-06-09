import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.ChaCha20.Spec.Xor
import LeanChachaPoly.ChaCha20.Spec.Keystream
import LeanChachaPoly.Poly1305.Spec

/-!
# ChaCha20-Poly1305 AEAD — Specification

RFC 8439 §2.8. Authenticated Encryption with Associated Data
constructed from ChaCha20 (encryption) and Poly1305 (authentication).

## The capstone theorem

  decrypt(encrypt(pt, aad)) = some pt

This is what the entire library exists to prove. The proof
decomposes into three sub-steps:

  1. `encrypt` appends `ct ‖ tag` where `ct = chacha20(1, pt)`
  2. `decrypt` recomputes the tag and finds it matches
     (by `poly1305` determinism — a pure function applied to
     the same inputs produces the same output)
  3. `decrypt` then returns `chacha20(1, ct) = chacha20(1, chacha20(1, pt)) = pt`
     by the ChaCha20 involution theorem

The entire proof is algebraic assembly — no new mathematical
content beyond what was proved in ChaCha20.Spec and Poly1305.Spec.

## Module structure

  Aead.Spec               ← this file: construction (encrypt/decrypt) only
  Aead.Correctness        ← roundtrip + length/shape capstones
  Aead.Security           ← authenticity: verify-before-decrypt, macData injectivity
  Aead.Spec.KeyDerivation ← derivePolyKey, padTo16/le64 lemmas
  Aead.Spec.MacData       ← macData injectivity lemmas
  Aead.Native             ← ByteArray bridge
-/
namespace Aead.Spec

open ChaCha20.Spec Poly1305.Spec

/-! ## Types -/

abbrev Key   := ChaCha20.Spec.Key
abbrev Nonce := ChaCha20.Spec.Nonce

/-! ## Poly1305 one-time key derivation (RFC 8439 §2.6) -/

/-- Run ChaCha20 with counter=0, take first 32 bytes as the
    Poly1305 key. The 32-byte length is guaranteed by
    `keystream_length`. -/
def derivePolyKey (key : Key) (nonce : Nonce) : Poly1305.Spec.Key :=
  let stream := keystream key nonce 0 64
  ⟨stream.take 32, by rw [List.length_take, keystream_length]; decide⟩

/-! ## MAC data construction (RFC 8439 §2.8) -/

/-- Pad a byte list to a multiple of 16 with zeros. The 16-alignment is enforced
    by the `Padded` return type. -/
def padTo16 (data : List UInt8) : Padded :=
  if h : data.length % 16 = 0 then ⟨data, h⟩
  else ⟨data ++ List.replicate (16 - data.length % 16) 0, by
    rw [List.length_append, List.length_replicate]; omega⟩

/-- Encode a Nat as 8 bytes, little-endian. -/
def le64 (n : Nat) : Bytes 8 :=
  ⟨(List.range 8).map fun i => UInt8.ofNat ((n >>> (i * 8)) % 256), by simp⟩

/-- Construct the Poly1305 authentication input per RFC 8439 §2.8.
    Layout: pad(aad) ‖ pad(ciphertext) ‖ len(aad) as 8-LE ‖ len(ct) as 8-LE.
    The total length is a multiple of 16 (`Padded`). -/
def macData (aad ciphertext : List UInt8) : Padded :=
  ⟨(padTo16 aad).val ++ (padTo16 ciphertext).val ++
   (le64 aad.length).val ++ (le64 ciphertext.length).val, by
    have h1 := (padTo16 aad).property
    have h2 := (padTo16 ciphertext).property
    have h3 := (le64 aad.length).property
    have h4 := (le64 ciphertext.length).property
    simp only [List.length_append]
    omega⟩

/-! ## Encrypt and decrypt -/

/-- AEAD encryption: returns ciphertext ‖ 16-byte tag. -/
def encrypt (key : Key) (nonce : Nonce)
    (plaintext aad : List UInt8) : List UInt8 :=
  let polyKey    := derivePolyKey key nonce
  let ciphertext := chacha20 key nonce 1 plaintext
  let tag        := poly1305 polyKey (macData aad ciphertext).val
  ciphertext ++ tag.val

/-- AEAD decryption: returns `some plaintext` on success,
    `none` if the tag does not match. -/
def decrypt (key : Key) (nonce : Nonce)
    (ciphertextAndTag aad : List UInt8) : Option (List UInt8) :=
  if ciphertextAndTag.length < 16 then none
  else
    let ctLen      := ciphertextAndTag.length - 16
    let ciphertext := ciphertextAndTag.take ctLen
    let recvTag    := ciphertextAndTag.drop ctLen
    let polyKey    := derivePolyKey key nonce
    let expTag     := poly1305 polyKey (macData aad ciphertext).val
    if recvTag == expTag.val then
      some (chacha20 key nonce 1 ciphertext)
    else none

/-!
This file is construction only. The properties live elsewhere:
- functional roundtrip / length facts — `Aead.Correctness` (`decrypt_encrypt`, …)
- authenticity — `Aead/Security.lean` (`decrypt_verifies`, `macData_inj`, bindings)
- `macData`/`padTo16`/`le64` structural lemmas — `Aead/Spec/{KeyDerivation,MacData}.lean`
-/

end Aead.Spec
