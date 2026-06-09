import Tests.Helpers
import LeanChachaPoly.Aead.Spec

/-!
# ChaCha20-Poly1305 AEAD Test Vectors — RFC 8439

Strict 1:1 port of `chacha20poly1305_test.go`:
  TestChaCha20Poly1305Poly1305KeyGen  (§2.6.2, A.4 #1–3)
  TestChaCha20Poly1305Encrypt         (§2.8.2)
  TestChaCha20Poly1305Decrypt         (A.5, Invalid Tag)
  TestChaCha20Poly1305                (encryption + decryption)

Go exposes `Poly1305KeyGen(firstBlock)`; the Lean library exposes the
equivalent `derivePolyKey key nonce` (ChaCha20 counter-0 keystream, first 32
bytes), so the KeyGen vectors are checked through it.
-/

open Tests.Helpers Aead.Spec

namespace Tests.ChaCha20Poly1305Test

/-! ## TestChaCha20Poly1305Poly1305KeyGen -/

structure KgTV where
  name     : String
  key      : Key
  nonce    : Nonce
  expected : List UInt8

def kgTvs : List KgTV := [
  { name := "§2.6.2"
    key   := mkKey   "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
    nonce := mkNonce "000000000001020304050607"
    expected := hexToList "8ad5a08b905f81cc815040274ab29471a833b637e3fd0da508dbb8e2fdd1a646" },
  { name := "A.4 #1"
    key   := mkKey   "0000000000000000000000000000000000000000000000000000000000000000"
    nonce := mkNonce "000000000000000000000000"
    expected := hexToList "76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7" },
  { name := "A.4 #2"
    key   := mkKey   "0000000000000000000000000000000000000000000000000000000000000001"
    nonce := mkNonce "000000000000000000000002"
    expected := hexToList "ecfa254f845f647473d3cb140da9e87606cb33066c447b87bc2666dde3fbb739" },
  { name := "A.4 #3"
    key   := mkKey   "1c9240a5eb55d38af333888604f6b5f0473917c1402b80099dca5cbc207075c0"
    nonce := mkNonce "000000000000000000000002"
    expected := hexToList "965e3bc6f9ec7ed9560808f4d229f94b137ff275ca9b3fcbdd59deaad23310ae" }
]

/-! ## TestChaCha20Poly1305Encrypt — §2.8.2 -/

def encKey   := mkKey   "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
def encNonce := mkNonce "070000004041424344454647"
def encAad   : List UInt8 := hexToList "50515253c0c1c2c3c4c5c6c7"
def encPt    : List UInt8 := asciiToList
  ("Ladies and Gentlemen of the class of '99: " ++
   "If I could offer you only one tip for the future, sunscreen would be it.")
def encWantCt : List UInt8 := hexToList
  ("d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d6" ++
   "3dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b36" ++
   "92ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc" ++
   "3ff4def08e4b7a9de576d26586cec64b6116")
def encWantTag : List UInt8 := hexToList "1ae10b594f09e26a7e902ecbd0600691"

/-! ## TestChaCha20Poly1305Decrypt — A.5 -/

def decKey   := mkKey   "1c9240a5eb55d38af333888604f6b5f0473917c1402b80099dca5cbc207075c0"
def decNonce := mkNonce "000000000102030405060708"
def decAad   : List UInt8 := hexToList "f33388860000000000004e91"
def decTag   : List UInt8 := hexToList "eead9d67890cbb22392336fea1851f38"
def decBadTag : List UInt8 := hexToList "42ad9d67890cbb22392336fea1851f38"
def decCt    : List UInt8 := hexToList
  ("64a0861575861af460f062c79be643bd5e805cfd345cf389f108670ac76c8cb2" ++
   "4c6cfc18755d43eea09ee94e382d26b0bdb7b73c321b0100d4f03b7f355894cf" ++
   "332f830e710b97ce98c8a84abd0b948114ad176e008d33bd60f982b1ff37c855" ++
   "9797a06ef4f0ef61c186324e2b3506383606907b6a7c02b0f9f6157b53c867e4" ++
   "b9166c767b804d46a59b5216cde7a4e99040c5a40433225ee282a1b0a06c523e" ++
   "af4534d7f83fa1155b0047718cbc546a0d072b04b3564eea1b422273f548271a" ++
   "0bb2316053fa76991955ebd63159434ecebb4e466dae5a1073a6727627097a10" ++
   "49e617d91d361094fa68f0ff77987130305beaba2eda04df997b714d6c6f2c29" ++
   "a6ad5cb4022b02709b")
def decWantPt : List UInt8 := hexToList
  ("496e7465726e65742d4472616674732061726520647261667420646f63756d65" ++
   "6e74732076616c696420666f722061206d6178696d756d206f6620736978206d" ++
   "6f6e74687320616e64206d617920626520757064617465642c207265706c6163" ++
   "65642c206f72206f62736f6c65746564206279206f7468657220646f63756d65" ++
   "6e747320617420616e792074696d652e20497420697320696e617070726f7072" ++
   "6961746520746f2075736520496e7465726e65742d4472616674732061732072" ++
   "65666572656e6365206d6174657269616c206f7220746f206369746520746865" ++
   "6d206f74686572207468616e206173202fe2809c776f726b20696e2070726f67" ++
   "726573732e2fe2809d")

/-! ## Runner -/

def runTests : IO Unit := do
  IO.println "ChaCha20-Poly1305 AEAD"

  group "TestChaCha20Poly1305Poly1305KeyGen" do
    let mut results := #[]
    for tv in kgTvs do
      results := results.push (← check tv.name tv.expected (derivePolyKey tv.key tv.nonce).val)
    return results.toList

  group "TestChaCha20Poly1305Encrypt" do
    let out := encrypt encKey encNonce encPt encAad
    return [
      ← check "§2.8.2 ciphertext" encWantCt  (out.take encPt.length),
      ← check "§2.8.2 tag"        encWantTag (out.drop encPt.length)
    ]

  group "TestChaCha20Poly1305Decrypt" do
    let a5 ← match decrypt decKey decNonce (decCt ++ decTag) decAad with
      | some pt => check "A.5 plaintext" decWantPt pt
      | none    => checkBool "A.5 decrypt succeeded" false
    let bad := checkBool "Invalid Tag rejected"
      (decrypt decKey decNonce (decCt ++ decBadTag) decAad == none)
    return [a5, ← bad]

  group "TestChaCha20Poly1305 (encryption + decryption)" do
    let ct := encrypt encKey encNonce encPt encAad
    let pt := decrypt encKey encNonce ct encAad
    return [← checkBool "roundtrip" (pt == some encPt)]

  IO.println ""

end Tests.ChaCha20Poly1305Test
