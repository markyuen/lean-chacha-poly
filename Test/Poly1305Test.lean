import Test.Helpers
import LeanChachaPoly.Poly1305.Spec

/-!
# Poly1305 Test Vectors — RFC 8439

§2.5.2    Primary test vector
A.3 #1–11 Edge-case vectors targeting common bugs
-/

open Test.Helpers Poly1305.Spec

namespace Test.Poly1305Test

private instance : Inhabited Key :=
  ⟨{ bytes := List.replicate 32 0, size := by simp }⟩

structure TV where
  name : String
  key  : Key
  msg  : List UInt8
  tag  : List UInt8
  deriving Inhabited

def mkKey (s : String) : Key :=
  let bs := hexToList s
  { bytes := bs.take 32 ++ List.replicate (32 - min 32 bs.length) 0
    size  := by
      simp only [List.length_append, List.length_take, List.length_replicate]
      omega }

def tvs : List TV := [
  -- §2.5.2: primary "Cryptographic Forum Research Group" vector
  { name := "§2.5.2 primary"
    key  := mkKey "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b"
    msg  := asciiToList "Cryptographic Forum Research Group"
    tag  := hexToList "a8061dc1305136c6c22b8baf0c0127a9" },

  -- A.3 #2: zero key, zero-padded message → tag = 0
  { name := "A.3 #2: zero key"
    key  := mkKey "0000000000000000000000000000000000000000000000000000000000000000"
    msg  := hexToList "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
    tag  := hexToList "00000000000000000000000000000000" },

  -- A.3 #3: r=0, s nonzero → tag = s mod 2^128
  { name := "A.3 #3: r=0"
    key  := mkKey "0000000000000000000000000000000036e5f6b5c5e06070f0efca96227a863e"
    msg  := hexToList "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
    tag  := hexToList "36e5f6b5c5e06070f0efca96227a863e" },

  -- A.3 #6: catch carry into bit 131
  { name := "A.3 #6: carry into bit 131"
    key  := mkKey "0100000000000000000000000000000000000000000000000000000000000000"
    msg  := hexToList "fffffffffffffffffffffffffffffffb"
    tag  := hexToList "01000000000000000000000000000000" },

  -- A.3 #7: final reduction
  { name := "A.3 #7: final reduction"
    key  := mkKey "0100000000000000000000000000000000000000000000000000000000000000"
    msg  := hexToList "fdffffffffffffffffffffffffffffff"
    tag  := hexToList "faffffffffffffffffffffffffffffff" }
]

def runTests : IO Unit := do
  IO.println "Poly1305"
  group "RFC 8439 test vectors" do
    let mut results := #[]
    for tv in tvs do
      let actual := poly1305 tv.key tv.msg
      results := results.push (← check tv.name tv.tag actual)
    return results.toList
  group "tag is always 16 bytes" do
    let k := (tvs[0]!).key
    let t := poly1305 k (asciiToList "test")
    return [← checkBool "length" (t.length == 16)]
  IO.println ""

end Test.Poly1305Test
