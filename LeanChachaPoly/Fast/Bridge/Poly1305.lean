import LeanChachaPoly.Fast.Poly1305
import LeanChachaPoly.Fast.Bridge.ByteList
import LeanChachaPoly.Fast.Bridge.Poly1305Limb
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

/-! ## Accumulation — Nat engine (Phase A, retained)

The GMP-`Nat` engine `accumulateNat` is superseded by the limb engine below
but retained with its own equivalence theorem: it is the direct, readable
witness that the block loop is the spec's fold, and `accumulate_eq_accumulateNat`
ties the two verified engines to each other. -/

/-- **Key lemma.** The Nat-engine block loop folds `Spec.step` over exactly
    the spec's block values (`toBlockNats` of the remaining suffix). -/
theorem accumulateNat_go_eq (r : Nat) (m : ByteArray) (off acc : Nat) :
    accumulateNat.go r m off acc
      = (Poly1305.Spec.toBlockNats (m.data.toList.drop off)).foldl
          (Poly1305.Spec.step r) acc := by
  fun_induction Poly1305.Fast.accumulateNat.go with
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

/-- **Key lemma.** The retained Nat engine equals the spec's accumulation. -/
theorem accumulateNat_eq (r : Nat) (m : ByteArray) :
    accumulateNat r m
      = Poly1305.Spec.accumulate r
          (Poly1305.Spec.blockNats (Poly1305.Spec.toBlocks m.data.toList)) := by
  rw [accumulateNat, accumulateNat_go_eq, Poly1305.Spec.blockNats_toBlocks,
    Poly1305.Spec.accumulate]
  simp

/-! ## Accumulation — limb engine -/

private theorem P_pos' : 0 < Poly1305.Spec.P := Poly1305.Spec.P_pos

private theorem P_lt : Poly1305.Spec.P < 2^130 := by
  unfold Poly1305.Spec.P
  omega

/-- **Supporting.** `Spec.step` on a frozen (`% P`) accumulator, with `r`
    reduced — the form the limb invariant produces. -/
private theorem step_freeze (r a b : Nat) :
    Poly1305.Spec.step r (a % Poly1305.Spec.P) b
      = ((a + b) * (r % Poly1305.Spec.P)) % Poly1305.Spec.P := by
  simp [Poly1305.Spec.step, Nat.add_mod, Nat.mul_mod]

/-- **Key lemma.** The limb block loop folds `Spec.step` over exactly the
    spec's block values: the loop invariant is the frozen value
    `limbsToNat h % P`, full blocks advance it by `stepLimbs`, and the
    trailing partial block is one `Spec.step` on the frozen value. -/
theorem accumulate_go_eq (r : Nat) (m : ByteArray)
    (r0 r1 r2 r3 r4 s1 s2 s3 s4 : UInt64)
    (hr0 : r0.toNat < 2^26) (hr1 : r1.toNat < 2^26) (hr2 : r2.toNat < 2^26)
    (hr3 : r3.toNat < 2^26) (hr4 : r4.toNat < 2^26)
    (hs1 : s1.toNat = 5 * r1.toNat) (hs2 : s2.toNat = 5 * r2.toNat)
    (hs3 : s3.toNat = 5 * r3.toNat) (hs4 : s4.toNat = 5 * r4.toNat)
    (hrv : r0.toNat + r1.toNat*2^26 + r2.toNat*2^52 + r3.toNat*2^78 + r4.toNat*2^104
      = r % Poly1305.Spec.P)
    (off : Nat) (h0 h1 h2 h3 h4 : UInt64)
    (hw : h0.toNat < 2^27 ∧ h1.toNat < 2^27 ∧ h2.toNat < 2^27 ∧ h3.toNat < 2^27
      ∧ h4.toNat < 2^27) :
    accumulate.go r m r0 r1 r2 r3 r4 s1 s2 s3 s4 off h0 h1 h2 h3 h4
      = (Poly1305.Spec.toBlockNats (m.data.toList.drop off)).foldl
          (Poly1305.Spec.step r)
          (limbsToNat h0 h1 h2 h3 h4 % Poly1305.Spec.P) := by
  revert hw
  fun_induction Poly1305.Fast.accumulate.go with
  | case1 off h0 h1 h2 h3 h4 hcond lo hi u0 u1 u2 u3 u4 d0 d1 d2 d3 d4 e1 e2 e3 e4 g0 ih =>
    intro hw
    obtain ⟨hw0, hw1, hw2, hw3, hw4⟩ := hw
    -- the intermediates are definitional let-fvars, so `rfl` discharges the
    -- equation hypotheses of `stepLimbs` against them
    obtain ⟨hval, hwo0, hwo1, hwo2, hwo3, hwo4⟩ :=
      stepLimbs r0 r1 r2 r3 r4 s1 s2 s3 s4 lo hi h0 h1 h2 h3 h4
        hr0 hr1 hr2 hr3 hr4 hs1 hs2 hs3 hs4 hw0 hw1 hw2 hw3 hw4
        u0 u1 u2 u3 u4 d0 d1 d2 d3 d4 e1 e2 e3 e4 g0
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rw [ih ⟨hwo0, hwo1, hwo2, hwo3, hwo4⟩]
    have hne : m.data.toList.drop off ≠ [] := by
      simp only [ne_eq, List.drop_eq_nil_iff]
      simp; omega
    have hblock : limbsToNat (g0 % 67108864) (e1 % 67108864 + g0 / 67108864)
        (e2 % 67108864) (e3 % 67108864) (e4 % 67108864) % Poly1305.Spec.P
        = Poly1305.Spec.step r (limbsToNat h0 h1 h2 h3 h4 % Poly1305.Spec.P)
            (Poly1305.Spec.blockToNat ⟨(m.data.toList.drop off).take 16,
              by simp [List.length_take, List.length_drop]; omega⟩) := by
      rw [hval, step_freeze, ← hrv, Poly1305.Spec.blockToNat, leToNat16_eq_leVal,
        ← load16_eq_leVal m off hcond]
      rfl
    rw [show Poly1305.Spec.toBlockNats (m.data.toList.drop off)
          = Poly1305.Spec.toBlockNats.go (m.data.toList.drop off) from rfl,
        Poly1305.Spec.go_cons _ hne,
        dif_pos (by simp [List.length_take, List.length_drop]; omega),
        List.foldl_cons, List.drop_drop, ← hblock]
    rfl
  | case2 off h0 h1 h2 h3 h4 hcond hlt =>
    intro _
    show Poly1305.Spec.step r (limbsToNat h0 h1 h2 h3 h4 % Poly1305.Spec.P)
        (loadFinal m off) = _
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
  | case3 off h0 h1 h2 h3 h4 hcond hlt =>
    intro _
    rw [List.drop_eq_nil_of_le (by simp; omega), Poly1305.Spec.toBlockNats_nil,
      List.foldl_nil]

/-- **Key lemma.** Fast accumulation equals the spec's, for every `r` (the
    engine's internal `r % P` reduction is absorbed by `Spec.step`'s own
    modular arithmetic). -/
theorem accumulate_eq (r : Nat) (m : ByteArray) :
    accumulate r m
      = Poly1305.Spec.accumulate r
          (Poly1305.Spec.blockNats (Poly1305.Spec.toBlocks m.data.toList)) := by
  have hrP : r % Poly1305.Spec.P < 2^130 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ P_pos') (Nat.le_of_lt P_lt)
  -- the nine limb registers round-trip through UInt64
  have l0 : (UInt64.ofNat (r % Poly1305.Spec.P % 67108864)).toNat
      = r % Poly1305.Spec.P % 67108864 := UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2^64 from rfl]; omega)
  have l1 : (UInt64.ofNat (r % Poly1305.Spec.P / 67108864 % 67108864)).toNat
      = r % Poly1305.Spec.P / 67108864 % 67108864 := UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2^64 from rfl]; omega)
  have l2 : (UInt64.ofNat (r % Poly1305.Spec.P / 4503599627370496 % 67108864)).toNat
      = r % Poly1305.Spec.P / 4503599627370496 % 67108864 :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2^64 from rfl]; omega)
  have l3 : (UInt64.ofNat (r % Poly1305.Spec.P / 302231454903657293676544 % 67108864)).toNat
      = r % Poly1305.Spec.P / 302231454903657293676544 % 67108864 :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2^64 from rfl]; omega)
  have l4 : (UInt64.ofNat (r % Poly1305.Spec.P / 20282409603651670423947251286016)).toNat
      = r % Poly1305.Spec.P / 20282409603651670423947251286016 :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2^64 from rfl]; omega)
  have m1 : (UInt64.ofNat (5 * (r % Poly1305.Spec.P / 67108864 % 67108864))).toNat
      = 5 * (r % Poly1305.Spec.P / 67108864 % 67108864) :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2^64 from rfl]; omega)
  have m2 : (UInt64.ofNat (5 * (r % Poly1305.Spec.P / 4503599627370496 % 67108864))).toNat
      = 5 * (r % Poly1305.Spec.P / 4503599627370496 % 67108864) :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2^64 from rfl]; omega)
  have m3 : (UInt64.ofNat (5 * (r % Poly1305.Spec.P / 302231454903657293676544 % 67108864))).toNat
      = 5 * (r % Poly1305.Spec.P / 302231454903657293676544 % 67108864) :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2^64 from rfl]; omega)
  have m4 : (UInt64.ofNat (5 * (r % Poly1305.Spec.P / 20282409603651670423947251286016))).toNat
      = 5 * (r % Poly1305.Spec.P / 20282409603651670423947251286016) :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2^64 from rfl]; omega)
  simp only [accumulate]
  rw [accumulate_go_eq r m _ _ _ _ _ _ _ _ _
    (by rw [l0]; omega) (by rw [l1]; omega) (by rw [l2]; omega)
    (by rw [l3]; omega) (by rw [l4]; omega)
    (by rw [m1, l1]) (by rw [m2, l2]) (by rw [m3, l3]) (by rw [m4, l4])
    (by rw [l0, l1, l2, l3, l4]; omega)
    0 _ _ _ _ _
    ⟨by decide, by decide, by decide, by decide, by decide⟩]
  rw [Poly1305.Spec.blockNats_toBlocks, Poly1305.Spec.accumulate]
  simp [limbsToNat]

/-- **Supporting.** The two verified engines agree on every input: the limb
    engine and the retained Nat engine are both equal to the spec, hence to
    each other. -/
theorem accumulate_eq_accumulateNat (r : Nat) (m : ByteArray) :
    accumulate r m = accumulateNat r m := by
  rw [accumulate_eq, accumulateNat_eq]

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
