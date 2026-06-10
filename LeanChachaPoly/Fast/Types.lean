import LeanChachaPoly.Subtypes
import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.Poly1305.Spec

/-!
# Fast implementation — types

`ByteArray`-backed mirrors of the spec's `Bytes n` subtypes, plus the
conversions between the two worlds. Same typing convention as the spec:
length invariants live in the type (`{ b : ByteArray // b.size = n }`),
so fixed-offset reads are total.

The bridge theorems are stated through `(·.data.toList)`: that is the
lemma-supported path from `ByteArray` to `List` in core Lean (the
recursive `ByteArray.toList` has essentially no lemmas).

This file is Mathlib-free; it is linked into the `test` and `bench`
executables.
-/

namespace Fast

/-- A `ByteArray` of exactly `n` bytes — the fast mirror of `Bytes n`. -/
abbrev BytesA (n : Nat) := { b : ByteArray // b.size = n }

namespace BytesA

/-- Total indexed read: the size invariant discharges the bounds obligation. -/
@[inline] def get {n : Nat} (b : BytesA n) (i : Nat) (h : i < n) : UInt8 :=
  b.val[i]'(by rw [b.property]; exact h)

/-- View a `BytesA n` as the spec's `Bytes n`. -/
def toSpec {n : Nat} (b : BytesA n) : Bytes n :=
  ⟨b.val.data.toList, by simp [b.property]⟩

/-- Build a `BytesA n` from the spec's `Bytes n`. -/
def ofSpec {n : Nat} (b : Bytes n) : BytesA n :=
  ⟨b.val.toByteArray, by simp [b.property]⟩

end BytesA

end Fast

namespace ChaCha20.Fast

/-- A 256-bit (32-byte) ChaCha20 key, as a `ByteArray`. -/
abbrev Key := _root_.Fast.BytesA 32

/-- A 96-bit (12-byte) nonce, as a `ByteArray`. -/
abbrev Nonce := _root_.Fast.BytesA 12

/-- Build a `Key` from a `ByteArray`, returning `none` unless it is exactly
    32 bytes. -/
def Key.ofBytes? (b : ByteArray) : Option Key :=
  if h : b.size = 32 then some ⟨b, h⟩ else none

/-- Build a `Nonce` from a `ByteArray`, returning `none` unless it is exactly
    12 bytes. -/
def Nonce.ofBytes? (b : ByteArray) : Option Nonce :=
  if h : b.size = 12 then some ⟨b, h⟩ else none

end ChaCha20.Fast

namespace Poly1305.Fast

/-- A 256-bit Poly1305 key (`r ‖ s`), as a `ByteArray`. -/
abbrev Key := _root_.Fast.BytesA 32

/-- Build a `Key` from a `ByteArray`, returning `none` unless it is exactly
    32 bytes. -/
def Key.ofBytes? (b : ByteArray) : Option Key :=
  if h : b.size = 32 then some ⟨b, h⟩ else none

end Poly1305.Fast
