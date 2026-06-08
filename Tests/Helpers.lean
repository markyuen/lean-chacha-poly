import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.Poly1305.Spec

/-!
# Test Helpers

Hex/ASCII decoding, byte/word comparison, grouped reporting, and smart
constructors for the `Key`/`Nonce` types used throughout the test vectors.
-/

namespace Tests.Helpers

/-! ## Decoding -/

def hexCharToNat (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexToBytes (s : String) : ByteArray :=
  let hexChars := s.toList.filter fun c =>
    ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
  ByteArray.mk (go hexChars #[])
where
  go : List Char → Array UInt8 → Array UInt8
    | c1 :: c2 :: rest, acc =>
      go rest (acc.push (UInt8.ofNat (hexCharToNat c1 * 16 + hexCharToNat c2)))
    | _, acc => acc

def hexToList (s : String) : List UInt8 := (hexToBytes s).data.toList

def asciiToList (s : String) : List UInt8 :=
  s.toList.map (fun c => UInt8.ofNat c.toNat)

/-! ## Formatting -/

def bytesToHex (bs : List UInt8) : String :=
  let d (n : Nat) : Char :=
    if n < 10 then Char.ofNat ('0'.toNat + n)
    else Char.ofNat ('a'.toNat + n - 10)
  bs.foldl (fun acc b =>
    acc ++ String.singleton (d (b.toNat / 16)) ++ String.singleton (d (b.toNat % 16))) ""

def wordsToHex (ws : Array UInt32) : String :=
  let hex (w : UInt32) : String :=
    let s := String.ofList (Nat.toDigits 16 w.toNat)
    "0x" ++ String.ofList (List.replicate (8 - min 8 s.length) '0') ++ s
  String.intercalate " " (ws.toList.map hex)

/-! ## Assertions -/

def check (name : String) (expected actual : List UInt8) : IO Bool := do
  if expected == actual then
    IO.println s!"  ✓ {name}"
    return true
  else
    IO.println s!"  ✗ {name}"
    IO.println s!"    expected: {bytesToHex expected}"
    IO.println s!"    actual:   {bytesToHex actual}"
    return false

def checkWords (name : String) (expected actual : Array UInt32) : IO Bool := do
  if expected == actual then
    IO.println s!"  ✓ {name}"
    return true
  else
    IO.println s!"  ✗ {name}"
    IO.println s!"    expected: {wordsToHex expected}"
    IO.println s!"    actual:   {wordsToHex actual}"
    return false

def checkBool (name : String) (cond : Bool) : IO Bool := do
  if cond then
    IO.println s!"  ✓ {name}"; return true
  else
    IO.println s!"  ✗ {name}"; return false

def group (name : String) (tests : IO (List Bool)) : IO Unit := do
  IO.println s!"  [{name}]"
  let r ← tests
  let ok := r.filter id |>.length
  IO.println s!"  {ok}/{r.length} passed"

/-! ## Smart constructors

Parse a hex string into the relevant key/nonce type, panicking on a
malformed (wrong-length) test vector — acceptable in a test harness. -/

instance : Inhabited ChaCha20.Spec.Key :=
  ⟨{ bytes := List.replicate 32 0, size := by simp }⟩

instance : Inhabited ChaCha20.Spec.Nonce :=
  ⟨{ bytes := List.replicate 12 0, size := by simp }⟩

instance : Inhabited Poly1305.Spec.Key :=
  ⟨{ bytes := List.replicate 32 0, size := by simp }⟩

def mkKey (s : String) : ChaCha20.Spec.Key :=
  (ChaCha20.Spec.Key.ofBytes? (hexToList s)).get!

def mkNonce (s : String) : ChaCha20.Spec.Nonce :=
  (ChaCha20.Spec.Nonce.ofBytes? (hexToList s)).get!

def mkPolyKey (s : String) : Poly1305.Spec.Key :=
  (Poly1305.Spec.Key.ofBytes? (hexToList s)).get!

end Tests.Helpers
