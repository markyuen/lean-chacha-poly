import LeanChachaPoly.Fast.Poly1305
import LeanChachaPoly.Fast.Bridge.ByteList
import LeanChachaPoly.Poly1305.Spec.Blocking
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.IntervalCases

/-!
# Fast bridge — Poly1305

Proves the fast `ByteArray` Poly1305 equal to `Poly1305.Spec.poly1305`
(capstone `poly1305_eq_spec`).

The accumulation arithmetic is *definitionally* shared (`Fast.accumulate`
folds `Spec.step`), so the bridge is entirely about byte handling:

- `leVal` (little-endian valuation of a byte list) is the common
  intermediate: the spec's positional `finRange` folds equal `leVal`
  (`posFold_eq_leVal`), the fast 16-byte `load16` equals `leVal` of the
  corresponding slice (`load16_eq_leVal`), and the fast trailing-bytes loop
  equals `leVal` of the suffix (`loadFinal_eq`).
- The block loop is then a `fun_induction` aligned with the spec's
  `toBlockNats` take-16/drop-16 recursion (`accumulate_go_eq`).
-/

namespace Poly1305.Fast

open Fast.Bridge

/-! ## Little-endian valuation -/

/-- Little-endian value of a byte list — the common intermediate between the
    spec's positional folds and the fast loads. -/
private def leVal : List UInt8 → Nat
  | [] => 0
  | b :: t => b.toNat + 256 * leVal t

/-- **Supporting.** The spec's positional byte fold is `leVal`. -/
private theorem posFold_eq_leVal (l : List UInt8) :
    (List.finRange l.length).foldl
      (fun acc i => acc + (l.get i).toNat * 2 ^ (i.val * 8)) 0 = leVal l := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    rw [Poly1305.Spec.foldl_add_eq_sum] at ih ⊢
    show 0 + (List.map
        (fun i : Fin (t.length + 1) => ((b :: t).get i).toNat * 2 ^ (i.val * 8))
        (List.finRange (t.length + 1))).sum = leVal (b :: t)
    rw [List.finRange_succ]
    simp only [List.get_eq_getElem] at ih
    simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def,
      List.get_eq_getElem, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
      List.getElem_cons_succ, Nat.zero_add, Nat.zero_mul, Nat.pow_zero, Nat.mul_one]
    rw [leVal, ← ih]
    have hfac : ∀ i : Fin t.length,
        t[i.val].toNat * 2 ^ ((i.val + 1) * 8)
          = 256 * (t[i.val].toNat * 2 ^ (i.val * 8)) := by
      intro i
      rw [Nat.add_mul, Nat.one_mul, Nat.pow_add]
      ring
    rw [List.map_congr_left (fun i _ => hfac i), List.sum_map_mul_left]
    omega

/-- **Supporting.** `finalBlockToNat` in `leVal` form. -/
private theorem finalBlockToNat_eq_leVal (fb : Poly1305.Spec.FinalBlock) :
    Poly1305.Spec.finalBlockToNat fb = leVal fb.val + 2 ^ (fb.val.length * 8) := by
  rw [Poly1305.Spec.finalBlockToNat, posFold_eq_leVal]

/-- **Supporting.** The cast variant of `posFold_eq_leVal`: substituting the
    length equation makes the `Fin.cast` definitionally the identity. -/
private theorem posFold_cast_eq_leVal (l : List UInt8) (n : Nat) (hl : l.length = n) :
    (List.finRange n).foldl
      (fun acc i => acc + (l.get (i.cast hl.symm)).toNat * 2 ^ (i.val * 8)) 0
      = leVal l := by
  subst hl
  exact posFold_eq_leVal l

/-- **Supporting.** `leToNat16` in `leVal` form. -/
private theorem leToNat16_eq_leVal (bs : Bytes 16) :
    Poly1305.Spec.leToNat16 bs = leVal bs.val := by
  rw [Poly1305.Spec.leToNat16]
  exact posFold_cast_eq_leVal bs.val 16 bs.property

/-! ## Loads -/

/-- **Supporting.** `leVal` of a nonempty suffix peels one byte. -/
private theorem leVal_drop (m : ByteArray) (j : Nat) (h : j < m.size) :
    leVal (m.data.toList.drop j)
      = (m[j]'h).toNat + 256 * leVal (m.data.toList.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons (l := m.data.toList) (i := j) (by simpa using h), leVal]
  simp only [Array.getElem_toList, ByteArray.getElem_eq_getElem_data]
  rfl

/-- **Supporting.** The trailing-bytes loop computes `leVal` of the suffix. -/
private theorem loadFinal_go_eq (m : ByteArray) (j shift acc : Nat) :
    loadFinal.go m j shift acc = acc + 2 ^ shift * leVal (m.data.toList.drop j) := by
  fun_induction Poly1305.Fast.loadFinal.go with
  | case1 j shift acc h ih =>
    rw [ih, leVal_drop m j h]
    rw [Nat.pow_add]
    ring
  | case2 j shift acc h =>
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    simp [leVal]

/-- **Supporting.** `loadFinal` is the spec's final-block value. -/
private theorem loadFinal_eq (m : ByteArray) (off : Nat) :
    loadFinal m off = leVal (m.data.toList.drop off) + 2 ^ ((m.size - off) * 8) := by
  rw [loadFinal, loadFinal_go_eq]
  simp

/-- **Supporting.** The `UInt64` 8-byte little-endian load, as a `Nat` value:
    the partial sums stay below `2⁶⁴`, so the wrapping arithmetic is exact. -/
private theorem load8_val (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (b0.toUInt64 + b1.toUInt64 * 256 + b2.toUInt64 * 65536
      + b3.toUInt64 * 16777216 + b4.toUInt64 * 4294967296
      + b5.toUInt64 * 1099511627776 + b6.toUInt64 * 281474976710656
      + b7.toUInt64 * 72057594037927936).toNat
      = b0.toNat + b1.toNat * 2^8 + b2.toNat * 2^16 + b3.toNat * 2^24
      + b4.toNat * 2^32 + b5.toNat * 2^40 + b6.toNat * 2^48 + b7.toNat * 2^56 := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt
  have h3 := b3.toNat_lt; have h4 := b4.toNat_lt; have h5 := b5.toNat_lt
  have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
  simp [UInt64.toNat_add, UInt64.toNat_mul]
  omega

/-- **Supporting.** `leVal` of an explicit 16-byte list. -/
private theorem leVal16 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    leVal [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15]
      = b0.toNat + b1.toNat * 2^8 + b2.toNat * 2^16 + b3.toNat * 2^24
      + b4.toNat * 2^32 + b5.toNat * 2^40 + b6.toNat * 2^48 + b7.toNat * 2^56
      + b8.toNat * 2^64 + b9.toNat * 2^72 + b10.toNat * 2^80 + b11.toNat * 2^88
      + b12.toNat * 2^96 + b13.toNat * 2^104 + b14.toNat * 2^112 + b15.toNat * 2^120 := by
  simp only [leVal]
  ring

/-- **Supporting.** A 16-byte slice as an explicit list. -/
private theorem slice16_eq (m : ByteArray) (off : Nat) (h : off + 16 ≤ m.size) :
    (m.data.toList.drop off).take 16
      = [m[off]'(by omega), m[off+1]'(by omega), m[off+2]'(by omega),
         m[off+3]'(by omega), m[off+4]'(by omega), m[off+5]'(by omega),
         m[off+6]'(by omega), m[off+7]'(by omega), m[off+8]'(by omega),
         m[off+8+1]'(by omega), m[off+8+2]'(by omega), m[off+8+3]'(by omega),
         m[off+8+4]'(by omega), m[off+8+5]'(by omega), m[off+8+6]'(by omega),
         m[off+8+7]'(by omega)] := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    have hk : k < 16 := by simp [List.length_take] at h1; omega
    simp only [List.getElem_take, List.getElem_drop, Array.getElem_toList,
      ← ByteArray.getElem_eq_getElem_data]
    interval_cases k <;> simp [Nat.add_assoc] <;> rfl

/-- **Key lemma.** The fast 16-byte load is `leVal` of the slice. -/
private theorem load16_eq_leVal (m : ByteArray) (off : Nat) (h : off + 16 ≤ m.size) :
    load16 m off h = leVal ((m.data.toList.drop off).take 16) := by
  rw [slice16_eq m off h, leVal16, load16, load8, load8, load8_val, load8_val]
  omega

/-! ## Key extraction -/

/-- **Supporting.** Fast `extractR` matches the spec. -/
theorem extractR_eq (key : Key) :
    extractR key = Poly1305.Spec.extractR key.toSpec := by
  rw [extractR, Poly1305.Spec.extractR]
  congr 1
  rw [leToNat16_eq_leVal, load16_eq_leVal]
  simp

/-- **Supporting.** Fast `extractS` matches the spec. -/
theorem extractS_eq (key : Key) :
    extractS key = Poly1305.Spec.extractS key.toSpec := by
  rw [extractS, Poly1305.Spec.extractS, leToNat16_eq_leVal, load16_eq_leVal]
  congr 1
  rw [List.take_of_length_le (by simp [key.property])]
  rfl

/-! ## Accumulation -/

/-- **Key lemma.** The fast block loop folds `Spec.step` over exactly the
    spec's block values (`toBlockNats` of the remaining suffix). -/
theorem accumulate_go_eq (r : Nat) (m : ByteArray) (off acc : Nat) :
    accumulate.go r m off acc
      = (Poly1305.Spec.toBlockNats (m.data.toList.drop off)).foldl
          (Poly1305.Spec.step r) acc := by
  fun_induction Poly1305.Fast.accumulate.go with
  | case1 off acc h ih =>
    rw [ih]
    have hne : m.data.toList.drop off ≠ [] := by
      simp only [ne_eq, List.drop_eq_nil_iff]
      simp; omega
    rw [show Poly1305.Spec.toBlockNats (m.data.toList.drop off)
          = Poly1305.Spec.toBlockNats.go (m.data.toList.drop off) from rfl,
        Poly1305.Spec.go_cons _ hne,
        dif_pos (by simp [List.length_take, List.length_drop]; omega),
        List.foldl_cons, List.drop_drop]
    congr 2
    rw [Poly1305.Spec.blockToNat, leToNat16_eq_leVal, load16_eq_leVal]
  | case2 off acc h hlt =>
    have hne : m.data.toList.drop off ≠ [] := by
      simp only [ne_eq, List.drop_eq_nil_iff]
      simp; omega
    rw [show Poly1305.Spec.toBlockNats (m.data.toList.drop off)
          = Poly1305.Spec.toBlockNats.go (m.data.toList.drop off) from rfl,
        Poly1305.Spec.go_cons _ hne,
        dif_neg (by simp [List.length_take, List.length_drop]; omega),
        List.foldl_cons, List.foldl_nil]
    congr 1
    rw [loadFinal_eq, Poly1305.Spec.finalBlockToNat, posFold_eq_leVal]
    show leVal (m.data.toList.drop off) + 2 ^ ((m.size - off) * 8)
        = leVal ((m.data.toList.drop off).take 16)
          + 2 ^ (((m.data.toList.drop off).take 16).length * 8)
    rw [List.take_of_length_le (by simp; omega)]
    simp
  | case3 off acc h hlt =>
    rw [List.drop_eq_nil_of_le (by simp; omega), Poly1305.Spec.toBlockNats_nil,
      List.foldl_nil]

/-- **Key lemma.** Fast accumulation equals the spec's. -/
theorem accumulate_eq (r : Nat) (m : ByteArray) :
    accumulate r m
      = Poly1305.Spec.accumulate r
          (Poly1305.Spec.blockNats (Poly1305.Spec.toBlocks m.data.toList)) := by
  rw [accumulate, accumulate_go_eq, Poly1305.Spec.blockNats_toBlocks,
    Poly1305.Spec.accumulate]
  simp

/-! ## Tag serialization -/

private theorem range16 :
    List.range 16 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := by decide

/-- **Supporting.** The unrolled tag pushes append the spec's 16 LE bytes. -/
theorem pushTag_toList (acc : ByteArray) (n : Nat) :
    (pushTag acc n).data.toList
      = acc.data.toList ++ (Poly1305.Spec.natToLe16 n).val := by
  simp [pushTag, Poly1305.Spec.natToLe16, range16]

/-! ## Capstone -/

/-- **Capstone.** The fast Poly1305 equals the spec on every input: the
    16-byte tag of a `ByteArray` message reads back as exactly the spec's
    tag on the same bytes. -/
theorem poly1305_eq_spec (key : Key) (msg : ByteArray) :
    (poly1305 key msg).data.toList
      = (Poly1305.Spec.poly1305 key.toSpec msg.data.toList).val := by
  rw [poly1305, Poly1305.Spec.poly1305, pushTag_toList, extractR_eq, extractS_eq,
    accumulate_eq]
  simp

end Poly1305.Fast
