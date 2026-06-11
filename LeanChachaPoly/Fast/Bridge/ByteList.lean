import LeanChachaPoly.Fast.Types
import Batteries.Data.ByteArray

/-!
# Fast bridge — ByteArray ↔ List glue

The bridge theorems relate `ByteArray`-valued fast functions to the spec's
`List UInt8` functions through `(·.data.toList)`: a `ByteArray`'s underlying
`Array` (`.data`), viewed as a `List` (`.toList`).

Core proves the facts this path needs, but one abstraction layer lower — on
`.data`, the `Array` — through `ByteArray.data_push`, `data_extract`,
`size_data`, and the like. Each lemma here composes one such core `data_*`
lemma with the matching `Array.toList_*` lemma to state the fact directly on
`(·.data.toList)`, under a single name. The composition is one `simp` step
(`toList_push` is `simp [ByteArray.data_push]`); naming it is purely for
ergonomics — the `rw` / `simp only` lists in the per-algorithm bridge proofs
need one lemma in the `(·.data.toList)` shape, not the two-layer pair. (A bare
`simp` closes these goals from core alone, without this kit.)

Only the cases the bridge cites by name are kept: `push` / `extract` /
`emptyWithCapacity` / `length` commuting with `(·.data.toList)`; `toList_inj`
(injectivity) with its helper `toByteArray_toList`; and the `toSpec` / `ofSpec`
subtype conversions, which are about the `BytesA` / `Bytes` project types and so
have no core analogue. `append` and `toByteArray` are already core in the
`(·.data.toList)` shape (`ByteArray.toList_data_append`,
`List.toList_data_toByteArray`, both `@[simp]`), and indexing / `==` go through
core's `Array.getElem_toList` and `Array` BEq directly, so none of those are
restated here.

Everything here is core/Batteries-level; the heavier Mathlib reasoning
lives in the per-algorithm bridge files.
-/

namespace Fast.Bridge

/-! ## `(·.data.toList)` vs ByteArray operations -/

@[simp] theorem toList_push (b : ByteArray) (u : UInt8) :
    (b.push u).data.toList = b.data.toList ++ [u] := by
  simp [ByteArray.data_push]

@[simp] theorem toList_extract (b : ByteArray) (s e : Nat) :
    (b.extract s e).data.toList = ((b.data.toList).drop s).take (e - s) := by
  simp [ByteArray.data_extract]

@[simp] theorem toList_emptyWithCapacity (n : Nat) :
    (ByteArray.emptyWithCapacity n).data.toList = [] := rfl

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
