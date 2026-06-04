namespace Test.Helpers

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

def bytesToHex (bs : List UInt8) : String :=
  let d (n : Nat) : Char :=
    if n < 10 then Char.ofNat ('0'.toNat + n)
    else Char.ofNat ('a'.toNat + n - 10)
  bs.foldl (fun acc b =>
    acc ++ String.singleton (d (b.toNat / 16)) ++ String.singleton (d (b.toNat % 16))) ""

def check (name : String) (expected actual : List UInt8) : IO Bool := do
  if expected == actual then
    IO.println s!"  ✓ {name}"
    return true
  else
    IO.println s!"  ✗ {name}"
    IO.println s!"    expected: {bytesToHex expected}"
    IO.println s!"    actual:   {bytesToHex actual}"
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

end Test.Helpers
