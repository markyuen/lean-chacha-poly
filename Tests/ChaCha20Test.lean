import Tests.Helpers
import LeanChachaPoly.ChaCha20.Spec

/-!
# ChaCha20 Test Vectors — RFC 8439

Strict 1:1 port of the Go suite:
  chacha20_internal_test.go  → TestChaCha20QuarterRound  (§2.1.1, §2.2.1)
  chacha20_test.go           → TestChaCha20BlockFunction (§2.3.2, A.1 #1–5)
                             → TestChaCha20XORWithKeyStream (§2.4.2, A.2 #1–3, enc+dec)
-/

open Tests.Helpers ChaCha20.Spec

namespace Tests.ChaCha20Test

/-! ## TestChaCha20QuarterRound -/

-- §2.1.1 — quarter round on four words.
def qr_2_1_1 : Bool :=
  quarterRound 0x11111111 0x01020304 0x9b8d6f43 0x01234567
    == (0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb)

-- §2.2.1 — quarter round on state positions (2, 7, 8, 13).
def qr_2_2_1_state : State := #[
  0x879531e0, 0xc5ecf37d, 0x516461b1, 0xc9a62f8a,
  0x44c20ef3, 0x3390af7f, 0xd9fc690b, 0x2a5f714c,
  0x53372767, 0xb00a5631, 0x974c541a, 0x359e9963,
  0x5c971061, 0x3d631689, 0x2098d9d6, 0x91dbd320]

def qr_2_2_1_expected : State := #[
  0x879531e0, 0xc5ecf37d, 0xbdb886dc, 0xc9a62f8a,
  0x44c20ef3, 0x3390af7f, 0xd9fc690b, 0xcfacafd2,
  0xe46bea80, 0xb00a5631, 0x974c541a, 0x359e9963,
  0x5c971061, 0xccc07c79, 0x2098d9d6, 0x91dbd320]

/-! ## TestChaCha20BlockFunction -/

-- §2.3.2
def block_2_3_2_key   := mkKey   "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
def block_2_3_2_nonce := mkNonce "000000090000004a00000000"
def block_2_3_2_expected : State := #[
  0xe4e7f110, 0x15593bd1, 0x1fdd0f50, 0xc47120a3,
  0xc7f4d1c7, 0x0368c033, 0x9aaa2204, 0x4e6cd4c3,
  0x466482d2, 0x09aa9f07, 0x05d7c214, 0xa2028bd9,
  0xd19c12b5, 0xb94e16de, 0xe883d0cb, 0x4e3c50a2]

-- A.1 #1
def block_a1_1_key   := mkKey   "0000000000000000000000000000000000000000000000000000000000000000"
def block_a1_1_nonce := mkNonce "000000000000000000000000"
def block_a1_1_expected : State := #[
  0xade0b876, 0x903df1a0, 0xe56a5d40, 0x28bd8653,
  0xb819d2bd, 0x1aed8da0, 0xccef36a8, 0xc70d778b,
  0x7c5941da, 0x8d485751, 0x3fe02477, 0x374ad8b8,
  0xf4b8436a, 0x1ca11815, 0x69b687c3, 0x8665eeb2]

-- A.1 #2 (counter = 1)
def block_a1_2_key   := mkKey   "0000000000000000000000000000000000000000000000000000000000000000"
def block_a1_2_nonce := mkNonce "000000000000000000000000"
def block_a1_2_expected : State := #[
  0xbee7079f, 0x7a385155, 0x7c97ba98, 0x0d082d73,
  0xa0290fcb, 0x6965e348, 0x3e53c612, 0xed7aee32,
  0x7621b729, 0x434ee69c, 0xb03371d5, 0xd539d874,
  0x281fed31, 0x45fb0a51, 0x1f0ae1ac, 0x6f4d794b]

-- A.1 #3 (counter = 1)
def block_a1_3_key   := mkKey   "0000000000000000000000000000000000000000000000000000000000000001"
def block_a1_3_nonce := mkNonce "000000000000000000000000"
def block_a1_3_expected : State := #[
  0x2452eb3a, 0x9249f8ec, 0x8d829d9b, 0xddd4ceb1,
  0xe8252083, 0x60818b01, 0xf38422b8, 0x5aaa49c9,
  0xbb00ca8e, 0xda3ba7b4, 0xc4b592d1, 0xfdf2732f,
  0x4436274e, 0x2561b3c8, 0xebdd4aa6, 0xa0136c00]

-- A.1 #4 (counter = 2)
def block_a1_4_key   := mkKey   "00ff000000000000000000000000000000000000000000000000000000000000"
def block_a1_4_nonce := mkNonce "000000000000000000000000"
def block_a1_4_expected : State := #[
  0xfb4dd572, 0x4bc42ef1, 0xdf922636, 0x327f1394,
  0xa78dea8f, 0x5e269039, 0xa1bebbc1, 0xcaf09aae,
  0xa25ab213, 0x48a6b46c, 0x1b9d9bcb, 0x092c5be6,
  0x546ca624, 0x1bec45d5, 0x87f47473, 0x96f0992e]

-- A.1 #5 (counter = 0)
def block_a1_5_key   := mkKey   "0000000000000000000000000000000000000000000000000000000000000000"
def block_a1_5_nonce := mkNonce "000000000000000000000002"
def block_a1_5_expected : State := #[
  0x374dc6c2, 0x3736d58c, 0xb904e24a, 0xcd3f93ef,
  0x88228b1a, 0x96a4dfb3, 0x5b76ab72, 0xc727ee54,
  0x0e0e978a, 0xf3145c95, 0x1b748ea8, 0xf786c297,
  0x99c28f5f, 0x628314e8, 0x398a19fa, 0x6ded1b53]

/-! ## TestChaCha20XORWithKeyStream -/

-- §2.4.2 — the "sunscreen" vector (counter = 1)
def enc_2_4_2_key   := mkKey   "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
def enc_2_4_2_nonce := mkNonce "000000000000004a00000000"
def enc_2_4_2_pt : List UInt8 := asciiToList
  ("Ladies and Gentlemen of the class of '99: " ++
   "If I could offer you only one tip for the future, sunscreen would be it.")
def enc_2_4_2_expected : List UInt8 := hexToList
  ("6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0b" ++
   "f91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d8" ++
   "07ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab7793736" ++
   "5af90bbf74a35be6b40b8eedf2785e42874d")

-- A.2 #1 — all-zero key/nonce, counter = 0, 64 zero bytes
def enc_a2_1_key   := mkKey   "0000000000000000000000000000000000000000000000000000000000000000"
def enc_a2_1_nonce := mkNonce "000000000000000000000000"
def enc_a2_1_pt : List UInt8 := List.replicate 64 0
def enc_a2_1_expected : List UInt8 := hexToList
  ("76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7" ++
   "da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586")

-- A.2 #2 — counter = 1
def enc_a2_2_key   := mkKey   "0000000000000000000000000000000000000000000000000000000000000001"
def enc_a2_2_nonce := mkNonce "000000000000000000000002"
def enc_a2_2_pt : List UInt8 := asciiToList
  ("Any submission to the IETF intended by the Contributor for publication as all " ++
   "or part of an IETF Internet-Draft or RFC and any statement made within the " ++
   "context of an IETF activity is considered an \"IETF Contribution\". Such " ++
   "statements include oral statements in IETF sessions, as well as written and " ++
   "electronic communications made at any time or place, which are addressed to")
def enc_a2_2_expected : List UInt8 := hexToList
  ("a3fbf07df3fa2fde4f376ca23e82737041605d9f4f4f57bd8cff2c1d4b7955ec" ++
   "2a97948bd3722915c8f3d337f7d370050e9e96d647b7c39f56e031ca5eb6250d" ++
   "4042e02785ececfa4b4bb5e8ead0440e20b6e8db09d881a7c6132f420e527950" ++
   "42bdfa7773d8a9051447b3291ce1411c680465552aa6c405b7764d5e87bea85a" ++
   "d00f8449ed8f72d0d662ab052691ca66424bc86d2df80ea41f43abf937d3259d" ++
   "c4b2d0dfb48a6c9139ddd7f76966e928e635553ba76c5c879d7b35d49eb2e62b" ++
   "0871cdac638939e25e8a1e0ef9d5280fa8ca328b351c3c765989cbcf3daa8b6c" ++
   "cc3aaf9f3979c92b3720fc88dc95ed84a1be059c6499b9fda236e7e818b04b0b" ++
   "c39c1e876b193bfe5569753f88128cc08aaa9b63d1a16f80ef2554d7189c411f" ++
   "5869ca52c5b83fa36ff216b9c1d30062bebcfd2dc5bce0911934fda79a86f6e6" ++
   "98ced759c3ff9b6477338f3da4f9cd8514ea9982ccafb341b2384dd902f3d1ab" ++
   "7ac61dd29c6f21ba5b862f3730e37cfdc4fd806c22f221")

-- A.2 #3 — counter = 42 (0x2a)
def enc_a2_3_key   := mkKey   "1c9240a5eb55d38af333888604f6b5f0473917c1402b80099dca5cbc207075c0"
def enc_a2_3_nonce := mkNonce "000000000000000000000002"
def enc_a2_3_pt : List UInt8 := hexToList
  ("2754776173206272696c6c69672c20616e642074686520736c6974687920746f" ++
   "7665730a446964206779726520616e642067696d626c6520696e207468652077" ++
   "6162653a0a416c6c206d696d737920776572652074686520626f726f676f7665" ++
   "732c0a416e6420746865206d6f6d65207261746873206f757467726162652e")
def enc_a2_3_expected : List UInt8 := hexToList
  ("62e6347f95ed87a45ffae7426f27a1df5fb69110044c0d73118effa95b01e5cf" ++
   "166d3df2d721caf9b21e5fb14c616871fd84c54f9d65b283196c7fe4f60553eb" ++
   "f39c6402c42234e32a356b3e764312a61a5532055716ead6962568f87d3f3f77" ++
   "04c6a8d1bcd1bf4d50d6154b6da731b187b58dfd728afa36757a797ac188d1")

/-! ## Runner -/

def runTests : IO Unit := do
  IO.println "ChaCha20"

  group "quarter round" do
    return [
      ← checkBool  "§2.1.1 four words"  qr_2_1_1,
      ← checkWords "§2.2.1 on state"    qr_2_2_1_expected
        (qr qr_2_2_1_state ⟨2, by omega⟩ ⟨7, by omega⟩ ⟨8, by omega⟩ ⟨13, by omega⟩)
    ]

  group "block function" do
    return [
      ← checkWords "§2.3.2"   block_2_3_2_expected (chacha20Block block_2_3_2_key block_2_3_2_nonce 1),
      ← checkWords "A.1 #1"   block_a1_1_expected  (chacha20Block block_a1_1_key  block_a1_1_nonce  0),
      ← checkWords "A.1 #2"   block_a1_2_expected  (chacha20Block block_a1_2_key  block_a1_2_nonce  1),
      ← checkWords "A.1 #3"   block_a1_3_expected  (chacha20Block block_a1_3_key  block_a1_3_nonce  1),
      ← checkWords "A.1 #4"   block_a1_4_expected  (chacha20Block block_a1_4_key  block_a1_4_nonce  2),
      ← checkWords "A.1 #5"   block_a1_5_expected  (chacha20Block block_a1_5_key  block_a1_5_nonce  0)
    ]

  group "XOR with keystream" do
    return [
      ← check "§2.4.2 sunscreen" enc_2_4_2_expected (chacha20 enc_2_4_2_key enc_2_4_2_nonce 1 enc_2_4_2_pt),
      ← check "A.2 #1"           enc_a2_1_expected  (chacha20 enc_a2_1_key  enc_a2_1_nonce  0 enc_a2_1_pt),
      ← check "A.2 #2"           enc_a2_2_expected (chacha20 enc_a2_2_key enc_a2_2_nonce 1 enc_a2_2_pt),
      ← check "A.2 #3"           enc_a2_3_expected  (chacha20 enc_a2_3_key  enc_a2_3_nonce  42 enc_a2_3_pt)
    ]

  group "encryption + decryption" do
    let ct := chacha20 enc_2_4_2_key enc_2_4_2_nonce 1 enc_2_4_2_pt
    let pt := chacha20 enc_2_4_2_key enc_2_4_2_nonce 1 ct
    return [← checkBool "roundtrip" (pt == enc_2_4_2_pt)]

  IO.println ""

end Tests.ChaCha20Test
