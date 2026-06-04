import Test.Helpers
import LeanChachaPoly.Aead.Spec

/-!
# ChaCha20-Poly1305 AEAD Test Vectors — RFC 8439

§2.6.2   Poly1305 key generation from ChaCha20
§2.8.2   Full AEAD encryption ("sunscreen")
A.5      AEAD decryption
-/

open Test.Helpers Aead.Spec ChaCha20.Spec

namespace Test.AeadTest

def mkKey (s : String) : Key := {
  bytes := hexToList s; size := by decide }

def mkNonce (s : String) : Nonce := {
  bytes := hexToList s; size := by decide }

-- ── §2.6.2 Poly1305 key generation ────────────────────────────

def kgKey   := mkKey   "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
def kgNonce := mkNonce "000000000001020304050607"
def kgExpected : List UInt8 := hexToList
  "8ad5a08b905f81cc815040274ab29471a833b637e3fd0da508dbb8e2fdd1a646"

-- ── §2.8.2 AEAD encryption ─────────────────────────────────────

def aeKey   := mkKey   "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
def aeNonce := mkNonce "070000004041424344454647"
def aeAad   : List UInt8 := hexToList "50515253c0c1c2c3c4c5c6c7"
def aePt    : List UInt8 := asciiToList
  ("Ladies and Gentlemen of the class of '99: " ++
   "If I could offer you only one tip for the future, sunscreen would be it.")
def aeExpectedCt : List UInt8 := hexToList
  ("d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d6" ++
   "3dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b36" ++
   "92ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc" ++
   "3ff4def08e4b7a9de576d26586cec64b6116")
def aeExpectedTag : List UInt8 := hexToList "1ae10b594f09e26a7e902ecbd0600691"
def aeExpected : List UInt8 := aeExpectedCt ++ aeExpectedTag

-- ── A.5 AEAD decryption ────────────────────────────────────────

def decKey   := mkKey
  "1c9240a5eb55d38af333888604f6b5f0473917c1402b80099dca5cbc207075c0"
def decNonce := mkNonce "000000000102030405060708"
def decAad   : List UInt8 := hexToList "f33388860000000000004e91"
def decCtTag : List UInt8 := hexToList
  ("64a0861575861af460f062c79be643bd5e805cfd345cf389f108670ac76c8cb2" ++
   "4c6cfc18755d43eea09ee94e382d26b0bdb7b73c321b0100d4f03b7f355894cf" ++
   "332f830e710b97ce98c8a84abd0b948114ad176e008d33bd60f982b1ff37c855" ++
   "9797a06ef4f0ef61c186324e2b3506383606907b6a7c02b0f9f6157b53c867e4" ++
   "b9166c767b804d46a59b5216cde7a4e99040c5a40433225ee282a1b0a06c523e" ++
   "af4534d7f83fa1155b0047718cbc546a0d072b04b3564eea1b422273f548271a" ++
   "0bb2316053fa76991955ebd63159434ecebb4e466dae5a1073a6727627097a10" ++
   "49e617d91d361094fa68f0ff77987130305beaba2eda04df997b714d6c6f2c29" ++
   "a6ad5cb4022b02709beead9d67890cbb22392336fea1851f38")

-- ── Test runner ────────────────────────────────────────────────

def runTests : IO Unit := do
  IO.println "ChaCha20-Poly1305 AEAD"

  group "§2.6.2 Poly1305 key generation" do
    let pk := derivePolyKey kgKey kgNonce
    return [← check "poly key" kgExpected pk.bytes]

  group "§2.8.2 AEAD encryption" do
    let out := encrypt aeKey aeNonce aePt aeAad
    return [
      ← check    "ciphertext + tag" aeExpected out,
      ← checkBool "output length"   (out.length == aePt.length + 16)
    ]

  group "§2.8.2 AEAD decryption" do
    match decrypt aeKey aeNonce aeExpected aeAad with
    | none    => return [← checkBool "decrypt succeeded" false]
    | some pt => return [← checkBool "plaintext matches" (pt == aePt)]

  group "A.5 AEAD decryption" do
    match decrypt decKey decNonce decCtTag decAad with
    | none    => return [← checkBool "A.5 decrypt succeeded" false]
    | some _  => return [← checkBool "A.5 decrypt succeeded" true]

  group "roundtrip" do
    let ct := encrypt aeKey aeNonce aePt aeAad
    let pt := decrypt aeKey aeNonce ct aeAad
    return [← checkBool "encrypt→decrypt = id" (pt == some aePt)]

  group "tamper detection" do
    let ct := encrypt aeKey aeNonce aePt aeAad
    -- Flip one bit in the ciphertext (not the tag)
    let tampered := ct.set 0 (ct.get! 0 ^^^ 0x01)
    let pt := decrypt aeKey aeNonce tampered aeAad
    return [← checkBool "tampered ct rejected" (pt == none)]

  group "empty plaintext" do
    let ct := encrypt aeKey aeNonce [] aeAad
    let pt := decrypt aeKey aeNonce ct aeAad
    return [
      ← checkBool "empty ct length = 16" (ct.length == 16),
      ← checkBool "empty roundtrip"      (pt == some [])
    ]

  group "AAD authentication" do
    let ct   := encrypt aeKey aeNonce aePt aeAad
    let bad  := decrypt aeKey aeNonce ct (aeAad ++ [0x00])
    return [← checkBool "wrong AAD rejected" (bad == none)]

  IO.println ""

end Test.AeadTest
