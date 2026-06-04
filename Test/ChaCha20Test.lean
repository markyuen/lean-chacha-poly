import Test.Helpers
import LeanChachaPoly.ChaCha20.Spec

/-!
# ChaCha20 Test Vectors — RFC 8439

§2.1.1  Quarter round
§2.3.2  Block function
§2.4.2  Full encryption ("sunscreen")
A.1     Additional block vectors
A.2     Additional encryption vectors
-/

open Test.Helpers ChaCha20.Spec

namespace Test.ChaCha20Test

-- ── Quarter round ──────────────────────────────────────────────

-- RFC 8439 §2.1.1
def qr_test : Bool :=
  quarterRound 0x11111111 0x01020304 0x9b8d6f43 0x01234567
  = (0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb)

-- ── Block function ─────────────────────────────────────────────

-- RFC 8439 §2.3.2 — ascending key, specific nonce, counter=1
def blockKey : Key := {
  bytes := hexToList "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
  size := by decide }

def blockNonce : Nonce := {
  bytes := hexToList "000000090000004a00000000"
  size := by decide }

def blockExpected : List UInt8 := hexToList
  ("10f1e7e4d13b5915500fdd1fa32071c4" ++
   "c7d1f4c733c06803042222aa9ac34d6e" ++
   "d28264460707aa09142c57d0d92b02a2" ++
   "b5129cd1de164eb9cbd083e8a2503c4e")

-- ── Encryption ("sunscreen") ───────────────────────────────────

-- RFC 8439 §2.4.2
def encKey : Key := {
  bytes := hexToList "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
  size := by decide }

def encNonce : Nonce := {
  bytes := hexToList "000000000000004a00000000"
  size := by decide }

def encPlaintext : List UInt8 := asciiToList
  ("Ladies and Gentlemen of the class of '99: " ++
   "If I could offer you only one tip for the future, sunscreen would be it.")

def encExpected : List UInt8 := hexToList
  ("6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0b" ++
   "f91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d8" ++
   "07ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab7793736" ++
   "5af90bbf74a35be6b40b8eedf2785e42874d")

-- ── Appendix A.1 — all-zero key/nonce/counter=0 ───────────────

def a1Key : Key := {
  bytes := hexToList "0000000000000000000000000000000000000000000000000000000000000000"
  size := by decide }

def a1Nonce : Nonce := {
  bytes := hexToList "000000000000000000000000"
  size := by decide }

def a1Expected : List UInt8 := hexToList
  ("76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7" ++
   "da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586")

-- ── Test runner ────────────────────────────────────────────────

def runTests : IO Unit := do
  IO.println "ChaCha20"
  group "quarter round (RFC 8439 §2.1.1)" do
    return [← checkBool "test vector" qr_test]
  group "block function (RFC 8439 §2.3.2)" do
    let actual := serializeBlock (chacha20Block blockKey blockNonce 1)
    return [← check "keystream" blockExpected actual]
  group "encryption (RFC 8439 §2.4.2)" do
    let actual := chacha20 encKey encNonce 1 encPlaintext
    return [
      ← check "ciphertext" encExpected actual,
      ← checkBool "length preserved" (actual.length == encPlaintext.length)
    ]
  group "involution" do
    let ct := chacha20 encKey encNonce 1 encPlaintext
    let pt := chacha20 encKey encNonce 1 ct
    return [← checkBool "encrypt∘encrypt = id" (pt == encPlaintext)]
  group "keystream (Appendix A.1)" do
    let actual := keystream a1Key a1Nonce 0 64
    return [← check "keystream" a1Expected actual]
  IO.println ""

end Test.ChaCha20Test
