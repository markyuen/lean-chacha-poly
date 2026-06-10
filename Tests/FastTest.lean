import Tests.Helpers
import Tests.ChaCha20Test
import Tests.Poly1305Test
import Tests.ChaCha20Poly1305Test
import LeanChachaPoly.Fast.Aead

/-!
# Fast implementation tests

Two layers:

1. **RFC 8439 vectors through the fast API** — the same vectors the spec
   suite uses (reused from the sibling test modules rather than re-pasted),
   run against `ChaCha20.Fast` / `Poly1305.Fast` / `Aead.Fast`.
2. **Differential fast-vs-spec checks** — deterministic pseudo-random
   inputs at block-boundary lengths, asserting the fast and spec outputs
   agree byte-for-byte. The bridge theorems prove this equality; running it
   exercises the *compiled* code paths (in-place `ByteArray.push`, extern
   indexing) that the kernel-level proofs do not execute.
-/

open Tests.Helpers

namespace Tests.FastTest

/-! ## Conversions -/

def fastKey (k : ChaCha20.Spec.Key) : ChaCha20.Fast.Key := Fast.BytesA.ofSpec k
def fastNonce (n : ChaCha20.Spec.Nonce) : ChaCha20.Fast.Nonce := Fast.BytesA.ofSpec n
def fastPolyKey (k : Poly1305.Spec.Key) : Poly1305.Fast.Key := Fast.BytesA.ofSpec k

/-! ## Deterministic pseudo-random inputs (LCG) -/

def lcgNext (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

/-- `n` pseudo-random bytes from `seed` (top byte of an LCG stream). -/
def randList (seed : UInt64) (n : Nat) : List UInt8 :=
  go seed n []
where
  go (s : UInt64) : Nat → List UInt8 → List UInt8
    | 0, acc => acc.reverse
    | k + 1, acc =>
      let s := lcgNext s
      go s k ((s >>> 56).toUInt8 :: acc)

def diffLengths : List Nat := [0, 1, 15, 16, 17, 63, 64, 65, 100, 1000, 4096]

/-! ## AEAD vectors (constants reused from `Tests.ChaCha20Poly1305Test`) -/

open Tests.ChaCha20Poly1305Test in
def aeadChecks : IO (List Bool) := do
  let encK := fastKey encKey
  let encN := fastNonce encNonce
  let out := Aead.Fast.encrypt encK encN encPt.toByteArray encAad.toByteArray
  let decK := fastKey decKey
  let decN := fastNonce decNonce
  let a5 ← match Aead.Fast.decrypt decK decN (decCt ++ decTag).toByteArray
      decAad.toByteArray with
    | some pt => check "A.5 plaintext" decWantPt pt.data.toList
    | none    => checkBool "A.5 decrypt succeeded" false
  return [
    ← check "§2.8.2 ciphertext" encWantCt (out.data.toList.take encPt.length),
    ← check "§2.8.2 tag" encWantTag (out.data.toList.drop encPt.length),
    a5,
    ← checkBool "Invalid Tag rejected"
      ((Aead.Fast.decrypt decK decN (decCt ++ decBadTag).toByteArray
        decAad.toByteArray).isNone),
    ← checkBool "roundtrip"
      ((Aead.Fast.decrypt encK encN out encAad.toByteArray).map (·.data.toList)
        == some encPt)
  ]

/-! ## Runner -/

def runTests : IO Unit := do
  IO.println "Fast implementation"

  group "block function (fast)" do
    let blk (k : ChaCha20.Spec.Key) (n : ChaCha20.Spec.Nonce) (ctr : UInt32) :
        Array UInt32 :=
      (ChaCha20.Fast.block (fastKey k) (fastNonce n) ctr).toState.val
    return [
      ← checkWords "§2.3.2" Tests.ChaCha20Test.block_2_3_2_expected
        (blk Tests.ChaCha20Test.block_2_3_2_key Tests.ChaCha20Test.block_2_3_2_nonce 1),
      ← checkWords "A.1 #1" Tests.ChaCha20Test.block_a1_1_expected
        (blk Tests.ChaCha20Test.block_a1_1_key Tests.ChaCha20Test.block_a1_1_nonce 0),
      ← checkWords "A.1 #2" Tests.ChaCha20Test.block_a1_2_expected
        (blk Tests.ChaCha20Test.block_a1_2_key Tests.ChaCha20Test.block_a1_2_nonce 1),
      ← checkWords "A.1 #3" Tests.ChaCha20Test.block_a1_3_expected
        (blk Tests.ChaCha20Test.block_a1_3_key Tests.ChaCha20Test.block_a1_3_nonce 1),
      ← checkWords "A.1 #4" Tests.ChaCha20Test.block_a1_4_expected
        (blk Tests.ChaCha20Test.block_a1_4_key Tests.ChaCha20Test.block_a1_4_nonce 2),
      ← checkWords "A.1 #5" Tests.ChaCha20Test.block_a1_5_expected
        (blk Tests.ChaCha20Test.block_a1_5_key Tests.ChaCha20Test.block_a1_5_nonce 0)
    ]

  group "XOR with keystream (fast)" do
    let enc (k : ChaCha20.Spec.Key) (n : ChaCha20.Spec.Nonce) (ctr : UInt32)
        (pt : List UInt8) : List UInt8 :=
      (ChaCha20.Fast.chacha20 (fastKey k) (fastNonce n) ctr pt.toByteArray).data.toList
    return [
      ← check "§2.4.2 sunscreen" Tests.ChaCha20Test.enc_2_4_2_expected
        (enc Tests.ChaCha20Test.enc_2_4_2_key Tests.ChaCha20Test.enc_2_4_2_nonce 1
          Tests.ChaCha20Test.enc_2_4_2_pt),
      ← check "A.2 #1" Tests.ChaCha20Test.enc_a2_1_expected
        (enc Tests.ChaCha20Test.enc_a2_1_key Tests.ChaCha20Test.enc_a2_1_nonce 0
          Tests.ChaCha20Test.enc_a2_1_pt),
      ← check "A.2 #2" Tests.ChaCha20Test.enc_a2_2_expected
        (enc Tests.ChaCha20Test.enc_a2_2_key Tests.ChaCha20Test.enc_a2_2_nonce 1
          Tests.ChaCha20Test.enc_a2_2_pt),
      ← check "A.2 #3" Tests.ChaCha20Test.enc_a2_3_expected
        (enc Tests.ChaCha20Test.enc_a2_3_key Tests.ChaCha20Test.enc_a2_3_nonce 42
          Tests.ChaCha20Test.enc_a2_3_pt)
    ]

  group "Poly1305 tag (fast)" do
    let mut results := #[]
    for tv in Tests.Poly1305Test.tvs do
      results := results.push (← check tv.name tv.tag
        (Poly1305.Fast.poly1305 (fastPolyKey tv.key) tv.msg.toByteArray).data.toList)
    return results.toList

  group "AEAD (fast)" aeadChecks

  group "limb vs nat engine" do
    -- The limb engine must agree with the Nat engine for every r (it reduces
    -- r % P internally; equal by Nat.mul_mod), including r ≥ P and r = 0.
    let keys : List (String × Nat) := [
      ("clamped key", Poly1305.Fast.extractR (fastPolyKey
        (Poly1305.Spec.Key.ofBytes? (randList 11 32)).get!)),
      ("r = 0", 0),
      ("r = P - 1", Poly1305.Spec.P - 1),
      ("r ≥ P", 2^130 + 12345)
    ]
    let mut results := #[]
    for (name, r) in keys do
      let ok := diffLengths.all fun len =>
        let m := (randList (UInt64.ofNat (3000 + len)) len).toByteArray
        Poly1305.Fast.accumulate r m == Poly1305.Fast.accumulateNat r m
      results := results.push (← checkBool name ok)
    return results.toList

  group "differential fast vs spec" do
    let specKey := (ChaCha20.Spec.Key.ofBytes? (randList 1 32)).get!
    let specNonce := (ChaCha20.Spec.Nonce.ofBytes? (randList 2 12)).get!
    let specPolyKey := (Poly1305.Spec.Key.ofBytes? (randList 3 32)).get!
    let fk := fastKey specKey
    let fn := fastNonce specNonce
    let fpk := fastPolyKey specPolyKey
    let mut results := #[]
    for len in diffLengths do
      let msg := randList (UInt64.ofNat (1000 + len)) len
      let msgBA := msg.toByteArray
      let aad := randList (UInt64.ofNat (2000 + len)) (len % 32)
      let aadBA := aad.toByteArray
      let okChaCha :=
        (ChaCha20.Fast.chacha20 fk fn 7 msgBA).data.toList
          == ChaCha20.Spec.chacha20 specKey specNonce 7 msg
      let okPoly :=
        (Poly1305.Fast.poly1305 fpk msgBA).data.toList
          == (Poly1305.Spec.poly1305 specPolyKey msg).val
      let fastCt := Aead.Fast.encrypt fk fn msgBA aadBA
      let specCt := Aead.Spec.encrypt specKey specNonce msg aad
      let okEnc := fastCt.data.toList == specCt
      let okDec :=
        (Aead.Fast.decrypt fk fn fastCt aadBA).map (·.data.toList)
          == Aead.Spec.decrypt specKey specNonce specCt aad
      -- Corrupt the first byte (ciphertext, or tag for empty messages):
      -- both sides must reject.
      let corrupted := match specCt with
        | [] => []
        | b :: rest => (b ^^^ 1) :: rest
      let okRej :=
        (Aead.Fast.decrypt fk fn corrupted.toByteArray aadBA).map (·.data.toList)
          == Aead.Spec.decrypt specKey specNonce corrupted aad
        && (Aead.Spec.decrypt specKey specNonce corrupted aad).isNone
      results := results.push
        (← checkBool s!"len {len}" (okChaCha && okPoly && okEnc && okDec && okRej))
    return results.toList

  IO.println ""

end Tests.FastTest
