import LeanChachaPoly.Fast.Types
import Batteries.Data.ByteArray

/-!
# Fast bridge — ByteArray ↔ List glue

The bridge theorems relate `ByteArray`-valued fast functions to the spec's
`List UInt8` functions through `(·.data.toList)` — the lemma-supported path
from `ByteArray` to `List` in core Lean. This file collects the small
rewriting kit used by all the bridge proofs: how `push` / `append` /
`extract` / `==` / indexing commute with `(·.data.toList)`, and that the
`toSpec`/`ofSpec` subtype conversions are mutually inverse.

Everything here is core/Batteries-level; the heavier Mathlib reasoning
lives in the per-algorithm bridge files.
-/

namespace Fast.Bridge

/-! ## `(·.data.toList)` vs ByteArray operations -/

@[simp] theorem toList_push (b : ByteArray) (u : UInt8) :
    (b.push u).data.toList = b.data.toList ++ [u] := by
  simp [ByteArray.data_push]

@[simp] theorem toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

@[simp] theorem toList_extract (b : ByteArray) (s e : Nat) :
    (b.extract s e).data.toList = ((b.data.toList).drop s).take (e - s) := by
  simp [ByteArray.data_extract]

@[simp] theorem toList_emptyWithCapacity (n : Nat) :
    (ByteArray.emptyWithCapacity n).data.toList = [] := rfl

@[simp] theorem toList_toByteArray (l : List UInt8) :
    l.toByteArray.data.toList = l := by
  simp [List.data_toByteArray]

theorem toByteArray_toList (b : ByteArray) :
    b.data.toList.toByteArray = b := by
  apply ByteArray.ext
  simp [List.data_toByteArray]

theorem toList_inj {a b : ByteArray} (h : a.data.toList = b.data.toList) :
    a = b := by
  rw [← toByteArray_toList a, ← toByteArray_toList b, h]

@[simp] theorem length_toList (b : ByteArray) :
    b.data.toList.length = b.size := by
  simp [ByteArray.size_data]

theorem getElem_toList (b : ByteArray) (i : Nat) (h : i < b.size) :
    b.data.toList[i]'(by simpa) = b[i] := by
  simp [ByteArray.getElem_eq_getElem_data]
  rfl

/-! ## Boolean equality -/

theorem beq_eq_toList_beq (a b : ByteArray) :
    (a == b) = (a.data.toList == b.data.toList) := by
  have hba : (a == b) = (a.data == b.data) := rfl
  rw [hba]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h; rw [h]
  · intro h; exact congrArg ByteArray.data (toList_inj h)

/-! ## `toSpec` / `ofSpec` -/

@[simp] theorem toSpec_ofSpec {n : Nat} (b : Bytes n) :
    (BytesA.ofSpec b).toSpec = b := by
  apply Subtype.ext
  simp [BytesA.ofSpec, BytesA.toSpec]

@[simp] theorem ofSpec_toSpec {n : Nat} (b : BytesA n) :
    BytesA.ofSpec b.toSpec = b := by
  apply Subtype.ext
  simp [BytesA.ofSpec, BytesA.toSpec, toByteArray_toList]

@[simp] theorem toSpec_val {n : Nat} (b : BytesA n) :
    (BytesA.toSpec b).val = b.val.data.toList := rfl

end Fast.Bridge
