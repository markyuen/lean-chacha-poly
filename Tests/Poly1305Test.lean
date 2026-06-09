import Tests.Helpers
import LeanChachaPoly.Poly1305.Spec

/-!
# Poly1305 Test Vectors — RFC 8439

Strict 1:1 port of `poly1305_test.go` (TestPoly1305GenerateTag):
§2.5.2 and Appendix A.3 #1–#11.
-/

open Tests.Helpers Poly1305.Spec

namespace Tests.Poly1305Test

structure TV where
  name : String
  key  : Key
  msg  : List UInt8
  tag  : List UInt8

-- The IETF "Any submission…" text used by A.3 #2 and #3.
def ietfText : List UInt8 := asciiToList
  ("Any submission to the IETF intended by the Contributor for publication as all " ++
   "or part of an IETF Internet-Draft or RFC and any statement made within the " ++
   "context of an IETF activity is considered an \"IETF Contribution\". Such " ++
   "statements include oral statements in IETF sessions, as well as written and " ++
   "electronic communications made at any time or place, which are addressed to")

def tvs : List TV := [
  { name := "§2.5.2"
    key  := mkPolyKey "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b"
    msg  := asciiToList "Cryptographic Forum Research Group"
    tag  := hexToList "a8061dc1305136c6c22b8baf0c0127a9" },

  { name := "A.3 #1"
    key  := mkPolyKey "0000000000000000000000000000000000000000000000000000000000000000"
    msg  := List.replicate 64 0
    tag  := hexToList "00000000000000000000000000000000" },

  { name := "A.3 #2"
    key  := mkPolyKey "0000000000000000000000000000000036e5f6b5c5e06070f0efca96227a863e"
    msg  := ietfText
    tag  := hexToList "36e5f6b5c5e06070f0efca96227a863e" },

  { name := "A.3 #3"
    key  := mkPolyKey "36e5f6b5c5e06070f0efca96227a863e00000000000000000000000000000000"
    msg  := ietfText
    tag  := hexToList "f3477e7cd95417af89a6b8794c310cf0" },

  { name := "A.3 #4"
    key  := mkPolyKey "1c9240a5eb55d38af333888604f6b5f0473917c1402b80099dca5cbc207075c0"
    msg  := hexToList
      ("2754776173206272696c6c69672c20616e642074686520736c6974687920746f" ++
       "7665730a446964206779726520616e642067696d626c6520696e207468652077" ++
       "6162653a0a416c6c206d696d737920776572652074686520626f726f676f7665" ++
       "732c0a416e6420746865206d6f6d65207261746873206f757467726162652e")
    tag  := hexToList "4541669a7eaaee61e708dc7cbcc5eb62" },

  { name := "A.3 #5"
    key  := mkPolyKey "0200000000000000000000000000000000000000000000000000000000000000"
    msg  := hexToList "ffffffffffffffffffffffffffffffff"
    tag  := hexToList "03000000000000000000000000000000" },

  { name := "A.3 #6"
    key  := mkPolyKey "02000000000000000000000000000000ffffffffffffffffffffffffffffffff"
    msg  := hexToList "02000000000000000000000000000000"
    tag  := hexToList "03000000000000000000000000000000" },

  { name := "A.3 #7"
    key  := mkPolyKey "0100000000000000000000000000000000000000000000000000000000000000"
    msg  := hexToList
      ("fffffffffffffffffffffffffffffffff0ffffffffffffffffffffffffffffff" ++
       "11000000000000000000000000000000")
    tag  := hexToList "05000000000000000000000000000000" },

  { name := "A.3 #8"
    key  := mkPolyKey "0100000000000000000000000000000000000000000000000000000000000000"
    msg  := hexToList
      ("fffffffffffffffffffffffffffffffffbfefefefefefefefefefefefefefefe" ++
       "01010101010101010101010101010101")
    tag  := hexToList "00000000000000000000000000000000" },

  { name := "A.3 #9"
    key  := mkPolyKey "0200000000000000000000000000000000000000000000000000000000000000"
    msg  := hexToList "fdffffffffffffffffffffffffffffff"
    tag  := hexToList "faffffffffffffffffffffffffffffff" },

  { name := "A.3 #10"
    key  := mkPolyKey "0100000000000000040000000000000000000000000000000000000000000000"
    msg  := hexToList
      ("e33594d7505e43b900000000000000003394d7505e4379cd0100000000000000" ++
       "00000000000000000000000000000000010000000000000000000000000000" ++
       "00")
    tag  := hexToList "14000000000000005500000000000000" },

  { name := "A.3 #11"
    key  := mkPolyKey "0100000000000000040000000000000000000000000000000000000000000000"
    msg  := hexToList
      ("e33594d7505e43b900000000000000003394d7505e4379cd0100000000000000" ++
       "00000000000000000000000000000000")
    tag  := hexToList "13000000000000000000000000000000" }
]

def runTests : IO Unit := do
  IO.println "Poly1305"
  group "TestPoly1305GenerateTag" do
    let mut results := #[]
    for tv in tvs do
      results := results.push (← check tv.name tv.tag (poly1305 tv.key tv.msg).val)
    return results.toList
  IO.println ""

end Tests.Poly1305Test
