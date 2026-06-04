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

  Aead.Spec               ← this file: construction + capstone
  Aead.Spec.KeyDerivation ← derivePolyKey correctness
  Aead.Spec.MacData       ← macData construction properties
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
  { bytes := stream.take 32,
    size  := by
      rw [List.length_take]
      rw [keystream_length]
      norm_num }

/-! ## MAC data construction (RFC 8439 §2.8) -/

/-- Pad a byte list to a multiple of 16 with zeros. -/
def padTo16 (data : List UInt8) : List UInt8 :=
  let rem := data.length % 16
  if rem = 0 then data
  else data ++ List.replicate (16 - rem) 0

/-- Encode a Nat as 8 bytes, little-endian. -/
def le64 (n : Nat) : List UInt8 :=
  (List.range 8).map fun i => UInt8.ofNat ((n >>> (i * 8)) % 256)

/-- Construct the Poly1305 authentication input per RFC 8439 §2.8.
    Layout: pad(aad) ‖ pad(ciphertext) ‖ len(aad) as 8-LE ‖ len(ct) as 8-LE -/
def macData (aad ciphertext : List UInt8) : List UInt8 :=
  padTo16 aad ++ padTo16 ciphertext ++
  le64 aad.length ++ le64 ciphertext.length

/-! ## Encrypt and decrypt -/

/-- AEAD encryption: returns ciphertext ‖ 16-byte tag. -/
def encrypt (key : Key) (nonce : Nonce)
    (plaintext aad : List UInt8) : List UInt8 :=
  let polyKey    := derivePolyKey key nonce
  let ciphertext := chacha20 key nonce 1 plaintext
  let tag        := poly1305 polyKey (macData aad ciphertext)
  ciphertext ++ tag

/-- AEAD decryption: returns `some plaintext` on success,
    `none` if the tag does not match. -/
def decrypt (key : Key) (nonce : Nonce)
    (ciphertextAndTag aad : List UInt8) : Option (List UInt8) :=
  if h : ciphertextAndTag.length < 16 then none
  else
    let ctLen      := ciphertextAndTag.length - 16
    let ciphertext := ciphertextAndTag.take ctLen
    let recvTag    := ciphertextAndTag.drop ctLen
    let polyKey    := derivePolyKey key nonce
    let expTag     := poly1305 polyKey (macData aad ciphertext)
    if recvTag == expTag then
      some (chacha20 key nonce 1 ciphertext)
    else none


/-! ================================================================
    CAPSTONE THEOREMS
    ================================================================ -/

/-! ### A1: THE ROUNDTRIP

    This is the central theorem the entire library exists to prove.

    Proof outline:
      Let ct  = chacha20 key nonce 1 plaintext
      Let tag = poly1305 (derivePolyKey key nonce) (macData aad ct)

      encrypt returns ct ++ tag                                  [unfold]

      In decrypt:
        ctLen = (ct ++ tag).length - 16
              = ct.length + 16 - 16
              = ct.length                                        [encrypt_length]
        ciphertext = (ct ++ tag).take ct.length = ct            [List.take_append]
        recvTag    = (ct ++ tag).drop ct.length = tag           [List.drop_append]
        expTag     = poly1305 ... (macData aad ct)              [unfold]
        recvTag == expTag                                        [rfl, same computation]
        result = some (chacha20 key nonce 1 ct)
               = some (chacha20 key nonce 1 (chacha20 key nonce 1 plaintext))
               = some plaintext                                  [chacha20_involutive]   -/
theorem decrypt_encrypt (key : Key) (nonce : Nonce)
    (plaintext aad : List UInt8) :
    decrypt key nonce (encrypt key nonce plaintext aad) aad
    = some plaintext := by
  simp only [decrypt, encrypt]
  -- Step 1: the output is long enough (not < 16)
  have hlen : ¬ (chacha20 key nonce 1 plaintext ++ _).length < 16 := by
    simp [List.length_append, Poly1305.Spec.poly1305_length]
    omega
  simp [hlen]
  -- Step 2: split off the tag correctly
  have hct := chacha20_length key nonce 1 plaintext
  simp [List.take_append_of_le_length (by omega),
        List.drop_append_of_le_length (by omega)]
  -- Step 3: tags match (same pure function, same inputs)
  simp
  -- Step 4: apply involution
  exact chacha20_involutive key nonce 1 plaintext

/-! ### A2: Ciphertext length -/
theorem encrypt_length (key : Key) (nonce : Nonce)
    (plaintext aad : List UInt8) :
    (encrypt key nonce plaintext aad).length
    = plaintext.length + 16 := by
  simp [encrypt, List.length_append,
        chacha20_length, poly1305_length]

/-! ### A3: Short ciphertext is rejected -/
theorem decrypt_short (key : Key) (nonce : Nonce) (aad : List UInt8)
    (ct : List UInt8) (h : ct.length < 16) :
    decrypt key nonce ct aad = none := by
  simp [decrypt, h]

/-! ### A4: AAD is authenticated but not encrypted

    The ciphertext bytes don't depend on the AAD. -/
theorem encrypt_ct_indep_of_aad (key : Key) (nonce : Nonce)
    (plaintext aad₁ aad₂ : List UInt8) :
    (encrypt key nonce plaintext aad₁).take plaintext.length =
    (encrypt key nonce plaintext aad₂).take plaintext.length := by
  simp [encrypt, chacha20_length,
        List.take_append_of_le_length (le_refl _)]

/-! ### A5: Empty plaintext roundtrip -/
theorem decrypt_encrypt_empty (key : Key) (nonce : Nonce) (aad : List UInt8) :
    decrypt key nonce (encrypt key nonce [] aad) aad = some [] := by
  exact decrypt_encrypt key nonce [] aad

end Aead.Spec
