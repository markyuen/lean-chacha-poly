import LeanChachaPoly.Fast.Types

/-!
# Poly1305 — fast implementation

The spec's field arithmetic is already GMP-backed `Nat` (a 130-bit mod-mul
per block); its cost is the `List` traversal around it — `take`/`drop`
allocation per block and a per-byte `foldl` over `List.finRange`. This
implementation eliminates that:

- the message stays a `ByteArray`; blocks are read by offset,
- each 16-byte block is loaded as two `UInt64` little-endian words combined
  into a `Nat` (two GMP limbs, no per-byte `Nat` operations),
- the accumulation loop is a tail recursion over the byte offset, reusing
  `Spec.step` (so the arithmetic is *definitionally* the spec's).

Loads are written with `+`/`*` rather than `|||`/`<<<` so the bridge proofs
reduce to linear arithmetic (`omega`); the compiler emits the same scalar
code either way.

Equivalence with `Poly1305.Spec.poly1305` is proved in
`LeanChachaPoly.Fast.Bridge.Poly1305` (`poly1305_eq_spec`).

This file is Mathlib-free; it is linked into the `test` and `bench`
executables.
-/

namespace Poly1305.Fast

open Poly1305.Spec (P clamp step)

/-! ## Little-endian loads -/

/-- Load 8 bytes at offset `off` as a little-endian `UInt64`. -/
@[inline] def load8 (m : ByteArray) (off : Nat) (h : off + 8 ≤ m.size) : UInt64 :=
  (m[off]'(by omega)).toUInt64
  + (m[off + 1]'(by omega)).toUInt64 * 256
  + (m[off + 2]'(by omega)).toUInt64 * 65536
  + (m[off + 3]'(by omega)).toUInt64 * 16777216
  + (m[off + 4]'(by omega)).toUInt64 * 4294967296
  + (m[off + 5]'(by omega)).toUInt64 * 1099511627776
  + (m[off + 6]'(by omega)).toUInt64 * 281474976710656
  + (m[off + 7]'(by omega)).toUInt64 * 72057594037927936

/-- Load 16 bytes at offset `off` as a little-endian `Nat` (< 2¹²⁸). -/
@[inline] def load16 (m : ByteArray) (off : Nat) (h : off + 16 ≤ m.size) : Nat :=
  (load8 m off (by omega)).toNat + (load8 m (off + 8) (by omega)).toNat * 2^64

/-- Load the trailing bytes `[off, m.size)` as a little-endian `Nat` and add
    the `2^(len·8)` high bit — the fast `finalBlockToNat`. -/
def loadFinal (m : ByteArray) (off : Nat) : Nat :=
  go off 0 0 + 2^((m.size - off) * 8)
where
  go (j : Nat) (shift : Nat) (acc : Nat) : Nat :=
    if h : j < m.size then
      go (j + 1) (shift + 8) (acc + (m[j]'h).toNat * 2^shift)
    else acc
  termination_by m.size - j

/-! ## Key extraction (RFC 8439 §2.5.1) -/

/-- Extract and clamp `r` (first 16 bytes of the key). -/
def extractR (key : Key) : Nat :=
  clamp (load16 key.val 0 (by rw [key.property]; omega))

/-- Extract `s` (last 16 bytes of the key). -/
def extractS (key : Key) : Nat :=
  load16 key.val 16 (by rw [key.property]; omega)

/-! ## Accumulation -/

/-- Accumulate the whole message: full 16-byte blocks get the `2¹²⁸` high
    bit, a trailing partial block gets `2^(len·8)`. Shaped to match the
    spec's `toBlockNats` take-16/drop-16 recursion. -/
def accumulate (r : Nat) (m : ByteArray) : Nat :=
  go 0 0
where
  go (off acc : Nat) : Nat :=
    if h : off + 16 ≤ m.size then
      go (off + 16) (step r acc (load16 m off h + 2^128))
    else if off < m.size then
      step r acc (loadFinal m off)
    else acc
  termination_by m.size - off

/-! ## Tag serialization -/

/-- Push a 128-bit `Nat` as 16 little-endian bytes — the fast `natToLe16`,
    unrolled. -/
def pushTag (acc : ByteArray) (n : Nat) : ByteArray :=
  let byte (i : Nat) : UInt8 := UInt8.ofNat ((n >>> (i * 8)) % 256)
  let acc := (((acc.push (byte 0)).push (byte 1)).push (byte 2)).push (byte 3)
  let acc := (((acc.push (byte 4)).push (byte 5)).push (byte 6)).push (byte 7)
  let acc := (((acc.push (byte 8)).push (byte 9)).push (byte 10)).push (byte 11)
  (((acc.push (byte 12)).push (byte 13)).push (byte 14)).push (byte 15)

/-! ## Full MAC -/

/-- Compute the Poly1305 tag: `(accumulate(r, m) + s) mod 2¹²⁸` as 16
    little-endian bytes. -/
def poly1305 (key : Key) (msg : ByteArray) : ByteArray :=
  let r := extractR key
  let s := extractS key
  pushTag (ByteArray.emptyWithCapacity 16) ((accumulate r msg + s) % 2^128)

end Poly1305.Fast
