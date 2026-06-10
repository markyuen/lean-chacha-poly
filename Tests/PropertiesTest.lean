import Tests.Helpers
import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.Poly1305.Spec
import LeanChachaPoly.Aead.Spec

/-!
# Property / edge-case tests

Beyond the RFC 8439 vectors (which the per-algorithm suites cover 1:1 with the
Go tests), these exercise behavioral properties: length invariants, the bare
`keystream` API, empty plaintext, AAD authentication, and ciphertext-body
tampering. The library states most of these as theorems
(`chacha20_length`, `poly1305_length`, `encrypt_length`,
`decrypt_encrypt`, …); here we check them computationally.
-/

open Tests.Helpers ChaCha20.Spec Poly1305.Spec Aead.Spec

namespace Tests.PropertiesTest

/-! ## Fixtures (reused RFC vectors) -/

def chaKey   := mkKey   "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
def chaNonce := mkNonce "000000000000004a00000000"
def chaPt    : List UInt8 := asciiToList
  ("Ladies and Gentlemen of the class of '99: " ++
   "If I could offer you only one tip for the future, sunscreen would be it.")

-- Appendix A.1 #1 keystream (all-zero key/nonce, counter 0).
def ksKey      := mkKey   "0000000000000000000000000000000000000000000000000000000000000000"
def ksNonce    := mkNonce "000000000000000000000000"
def ksExpected : List UInt8 := hexToList
  ("76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7" ++
   "da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586")

def polyKey := mkPolyKey "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b"

def aeKey   := mkKey   "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
def aeNonce := mkNonce "070000004041424344454647"
def aeAad   : List UInt8 := hexToList "50515253c0c1c2c3c4c5c6c7"

/-! ## Runner -/

def runTests : IO Unit := do
  IO.println "Properties / edge cases"

  group "ChaCha20" do
    let ct := chacha20 chaKey chaNonce 1 chaPt
    return [
      ← checkBool "length preserved" (ct.length == chaPt.length),
      ← check     "keystream (A.1 #1)" ksExpected (keystream ksKey ksNonce 0 64)
    ]

  group "Poly1305" do
    let tag := (poly1305 polyKey (asciiToList "test")).val
    return [← checkBool "tag is always 16 bytes" (tag.length == 16)]

  group "ChaCha20-Poly1305 AEAD" do
    let ct := encrypt aeKey aeNonce chaPt aeAad
    let lengthOk := ct.length == chaPt.length + 16
    -- Flip one bit in the ciphertext body (not the tag).
    let tampered := ct.set 0 (ct[0]! ^^^ 0x01)
    let tamperRejected := decrypt aeKey aeNonce tampered aeAad == none
    -- Wrong AAD must fail authentication.
    let aadRejected := decrypt aeKey aeNonce ct (aeAad ++ [0x00]) == none
    -- Empty plaintext: ciphertext is just the 16-byte tag and roundtrips.
    let emptyCt := encrypt aeKey aeNonce [] aeAad
    let emptyRoundtrip := decrypt aeKey aeNonce emptyCt aeAad == some []
    return [
      ← checkBool "output length = pt + 16"      lengthOk,
      ← checkBool "tampered ciphertext rejected" tamperRejected,
      ← checkBool "wrong AAD rejected"           aadRejected,
      ← checkBool "empty ciphertext length = 16" (emptyCt.length == 16),
      ← checkBool "empty plaintext roundtrip"    emptyRoundtrip
    ]

  IO.println ""

end Tests.PropertiesTest
