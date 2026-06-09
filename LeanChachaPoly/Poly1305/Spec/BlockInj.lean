import LeanChachaPoly.Poly1305.Spec
import LeanChachaPoly.Poly1305.Spec.Blocking
import LeanChachaPoly.Poly1305.Spec.Security
import Mathlib

/-!
# Poly1305 Block-Encoding Injectivity

The `|= 1 << (8 * len)` step (RFC 8439 §2.5.1) makes block encoding injective:
distinct chunks — whether they differ in content or in length — map to distinct
field elements. This is the structural fact behind Poly1305's collision
resistance (it feeds `toBlocks_inj`, lifting the forgery bound to messages).

We work through a clean recursive little-endian value `leVal`, prove it is
bounded (`< 256^len`) and injective on equal-length lists, then read off
`finalBlockToNat`'s injectivity from the disjoint high-bit ranges.
-/

namespace Poly1305.Spec

/-- Recursive little-endian value of a byte list: `Σ bytesᵢ · 256ⁱ`. -/
def leVal : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leVal bs

/-- Folding `(acc + g i)` over a list is the running sum. -/
private theorem foldl_add_eq_sum {α : Type*} (l : List α) (g : α → Nat) (init : Nat) :
    l.foldl (fun acc i => acc + g i) init = init + (l.map g).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih => simp [ih]; ring

/-- `leVal` fits in `len` base-256 digits. -/
theorem leVal_lt (a : List UInt8) : leVal a < 256 ^ a.length := by
  induction a with
  | nil => simp [leVal]
  | cons c cs ih =>
    rw [leVal, List.length_cons, pow_succ]
    have := c.toNat_lt
    omega

/-- `leVal` is injective on lists of equal length: the low byte is the value
    mod 256, and the rest follows by induction. -/
theorem leVal_inj (a b : List UInt8) (hlen : a.length = b.length)
    (h : leVal a = leVal b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons d ds => simp at hlen
  | cons c cs ih =>
    cases b with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [leVal, leVal] at h
      have h1 := c.toNat_lt
      have h2 := d.toNat_lt
      have hcd : c.toNat = d.toNat := by omega
      have hrest : leVal cs = leVal ds := by omega
      rw [UInt8.toNat_inj.mp hcd, ih ds hlen hrest]

/-- The positional sum (non-dependent, over `Finset.range` and `getD`) equals
    the recursive `leVal`. -/
private theorem rangeSum_eq_leVal (a : List UInt8) :
    (∑ i ∈ Finset.range a.length, (a.getD i default).toNat * 256 ^ i) = leVal a := by
  induction a with
  | nil => simp [leVal]
  | cons c cs ih =>
    rw [List.length_cons, Finset.sum_range_succ', leVal]
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one]
    rw [Nat.add_comm]
    congr 1
    rw [← ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring

/-- The indexed positional sum (over `Fin`) matches the non-dependent range sum. -/
private theorem finSum_eq_rangeSum (a : List UInt8) :
    (∑ i : Fin a.length, (a.get i).toNat * 256 ^ i.val)
      = ∑ i ∈ Finset.range a.length, (a.getD i default).toNat * 256 ^ i := by
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [List.get_eq_getElem, ← List.getD_eq_getElem a default i.isLt] :
      ∀ i ∈ (Finset.univ : Finset (Fin a.length)),
        (a.get i).toNat * 256 ^ i.val = (a.getD i.val default).toNat * 256 ^ i.val)]
  exact Fin.sum_univ_eq_sum_range (fun j => (a.getD j default).toNat * 256 ^ j) a.length

/-- `finalBlockToNat` as recursive value plus the length-encoding high bit. -/
theorem finalBlockToNat_eq (a : List UInt8) (h : a.length ≤ 16) :
    finalBlockToNat ⟨a, h⟩ = leVal a + 2 ^ (a.length * 8) := by
  show (List.finRange a.length).foldl
      (fun acc i => acc + (a.get i).toNat * 2 ^ (i.val * 8)) 0 + 2 ^ (a.length * 8)
    = leVal a + 2 ^ (a.length * 8)
  congr 1
  rw [foldl_add_eq_sum, Nat.zero_add, ← Fin.sum_univ_def]
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [show (2 : Nat) ^ (i.val * 8) = 256 ^ i.val from by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul, Nat.mul_comm]] :
      ∀ i ∈ (Finset.univ : Finset (Fin a.length)),
        (a.get i).toNat * 2 ^ (i.val * 8) = (a.get i).toNat * 256 ^ i.val)]
  rw [finSum_eq_rangeSum, rangeSum_eq_leVal]

/-- **Chunk-encoding injectivity (RFC 8439 §2.5.1).** Distinct final blocks —
    whether differing in content or length — map to distinct field elements.
    The `2^(8·len)` high bit puts the value in `[2^(8·len), 2^(8·len+1))`, so
    the length is determined, and within a length the content sum is injective. -/
theorem finalBlockToNat_inj (a b : List UInt8) (ha : a.length ≤ 16) (hb : b.length ≤ 16)
    (h : finalBlockToNat ⟨a, ha⟩ = finalBlockToNat ⟨b, hb⟩) : a = b := by
  rw [finalBlockToNat_eq, finalBlockToNat_eq] at h
  have hla : leVal a < 2 ^ (a.length * 8) := by
    have := leVal_lt a; rwa [show (256 : Nat) ^ a.length = 2 ^ (a.length * 8) from by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul, Nat.mul_comm]] at this
  have hlb : leVal b < 2 ^ (b.length * 8) := by
    have := leVal_lt b; rwa [show (256 : Nat) ^ b.length = 2 ^ (b.length * 8) from by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul, Nat.mul_comm]] at this
  have hlen : a.length = b.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (2 : Nat) ^ (a.length * 8 + 1) ≤ 2 ^ (b.length * 8) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have heq : (2 : Nat) ^ (a.length * 8 + 1) = 2 ^ (a.length * 8) + 2 ^ (a.length * 8) := by
        rw [pow_succ]; ring
      omega
    · have hle : (2 : Nat) ^ (b.length * 8 + 1) ≤ 2 ^ (a.length * 8) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have heq : (2 : Nat) ^ (b.length * 8 + 1) = 2 ^ (b.length * 8) + 2 ^ (b.length * 8) := by
        rw [pow_succ]; ring
      omega
  rw [hlen] at h
  exact leVal_inj a b hlen (by omega)

/-- The sketch's form of chunk-encoding injectivity: chunks differing in content
    **or** length get distinct encodings. -/
theorem finalBlock_encoding_distinct (a b : List UInt8) (ha : a.length ≤ 16)
    (hb : b.length ≤ 16) (hne : a ≠ b) :
    finalBlockToNat ⟨a, ha⟩ ≠ finalBlockToNat ⟨b, hb⟩ :=
  fun h => hne (finalBlockToNat_inj a b ha hb h)

/-! ## Full-block injectivity and range separation -/

/-- `leToNat16` is the recursive little-endian value. -/
private theorem leToNat16_eq_leVal (bs : List UInt8) (h : bs.length = 16) :
    leToNat16 ⟨bs, h⟩ = leVal bs := by
  show (List.finRange 16).foldl
      (fun acc i => acc + (bs.get (i.cast h.symm)).toNat * 2 ^ (i.val * 8)) 0 = leVal bs
  rw [foldl_add_eq_sum, Nat.zero_add, ← Fin.sum_univ_def]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin 16)),
      (bs.get (i.cast h.symm)).toNat * 2 ^ (i.val * 8)
        = (bs.getD i.val default).toNat * 256 ^ i.val := by
    intro i _
    have hi : i.val < bs.length := by rw [h]; exact i.isLt
    have hget : bs.get (i.cast h.symm) = bs.getD i.val default := by
      rw [List.getD_eq_getElem bs default hi, List.get_eq_getElem]
      simp only [Fin.val_cast]
    rw [hget, show (2 : Nat) ^ (i.val * 8) = 256 ^ i.val from by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul, Nat.mul_comm]]
  rw [Finset.sum_congr rfl hterm,
    Fin.sum_univ_eq_sum_range (fun j => (bs.getD j default).toNat * 256 ^ j) 16, ← h]
  exact rangeSum_eq_leVal bs

/-- Full 16-byte blocks inject (the `2¹²⁸` high bit is constant, so the content
    determines the bytes). -/
theorem blockToNat_inj (a b : List UInt8) (ha : a.length = 16) (hb : b.length = 16)
    (h : blockToNat ⟨a, ha⟩ = blockToNat ⟨b, hb⟩) : a = b := by
  unfold blockToNat at h
  rw [leToNat16_eq_leVal a ha, leToNat16_eq_leVal b hb] at h
  exact leVal_inj a b (ha.trans hb.symm) (by omega)

/-- A short final block stays below `2¹²⁸` — disjoint from full blocks
    (`≥ 2¹²⁸`), so the two kinds never collide. -/
private theorem finalBlock_lt (y : List UInt8) (hy : y.length ≤ 16) (hy' : y.length ≠ 16) :
    finalBlockToNat ⟨y, hy⟩ < 2 ^ 128 := by
  rw [finalBlockToNat_eq]
  have hlt : leVal y < 2 ^ (y.length * 8) := by
    have := leVal_lt y; rwa [show (256 : Nat) ^ y.length = 2 ^ (y.length * 8) from by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul, Nat.mul_comm]] at this
  have h2 : (2 : Nat) ^ (y.length * 8) + 2 ^ (y.length * 8) = 2 ^ (y.length * 8 + 1) := by
    rw [pow_succ]; ring
  have hle : (2 : Nat) ^ (y.length * 8 + 1) ≤ 2 ^ 128 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ## `toBlocks` injectivity -/

private theorem goInj (M : List UInt8) :
    ∀ (M' : List UInt8), toBlockNats.go M = toBlockNats.go M' → M = M' := by
  induction M using toBlockNats.go.induct with
  | case1 =>
    intro M' h
    rw [show toBlockNats.go [] = [] from by simp [toBlockNats.go]] at h
    by_contra hne
    rw [go_cons M' (fun e => hne e.symm)] at h
    split at h <;> simp at h
  | case2 bs hne _block rest hlen ih =>
    intro M' h
    rw [go_cons bs hne, dif_pos hlen] at h
    rcases eq_or_ne M' [] with rfl | hM'
    · simp [toBlockNats.go] at h
    · rw [go_cons M' hM'] at h
      split at h
      · rename_i hlen'
        rw [List.cons.injEq] at h
        obtain ⟨hhead, htail⟩ := h
        have htk : bs.take 16 = M'.take 16 := blockToNat_inj _ _ hlen hlen' hhead
        have hdr : bs.drop 16 = M'.drop 16 := ih _ htail
        calc bs = bs.take 16 ++ bs.drop 16 := (List.take_append_drop 16 bs).symm
          _ = M'.take 16 ++ M'.drop 16 := by rw [htk, hdr]
          _ = M' := List.take_append_drop 16 M'
      · rename_i hlen'
        rw [List.cons.injEq] at h
        have hge := blockToNat_ge ⟨bs.take 16, hlen⟩
        have hlt := finalBlock_lt (M'.take 16) (List.length_take_le 16 M')
          (by rw [List.length_take] at hlen' ⊢; omega)
        omega
  | case3 bs hne _block hlen =>
    intro M' h
    rw [go_cons bs hne, dif_neg hlen] at h
    have hbs : bs.length < 16 := by
      rw [List.length_take] at hlen; omega
    rcases eq_or_ne M' [] with rfl | hM'
    · simp [toBlockNats.go] at h
    · rw [go_cons M' hM'] at h
      split at h
      · rename_i hlen'
        rw [List.cons.injEq] at h
        have hge := blockToNat_ge ⟨M'.take 16, hlen'⟩
        have hlt := finalBlock_lt (bs.take 16) (List.length_take_le 16 bs)
          (by rw [List.length_take]; omega)
        omega
      · rename_i hlen'
        rw [List.cons.injEq] at h
        have hfin : bs.take 16 = M'.take 16 :=
          finalBlockToNat_inj _ _ (List.length_take_le 16 bs) (List.length_take_le 16 M') h.1
        have e1 : bs.take 16 = bs := List.take_of_length_le (by omega)
        have e2 : M'.take 16 = M' := by
          rw [List.length_take] at hlen'
          exact List.take_of_length_le (by omega)
        rw [e1, e2] at hfin
        exact hfin

/-- The numeric block engine is injective: distinct messages expand to distinct
    block-`Nat` lists. The high-bit padding makes block boundaries and the final
    length unambiguous. -/
theorem toBlockNats_inj (M M' : List UInt8) (h : toBlockNats M = toBlockNats M') : M = M' :=
  goInj M M' h

/-- **`toBlocks` is injective**: distinct messages expand to distinct typed block
    structures, so the polynomial-hash collision bound lifts from block lists to
    messages. -/
theorem toBlocks_inj (M M' : List UInt8) (h : toBlocks M = toBlocks M') : M = M' :=
  toBlockNats_inj M M' (by rw [← blockNats_toBlocks, ← blockNats_toBlocks]; exact congrArg blockNats h)

open Polynomial in
/-- **Message-level forgery bound (distinct messages).** With `toBlocks_inj`
    closing the lift, the almost-universal bound holds for any two distinct
    messages `M ≠ M'`, not just distinct block expansions. -/
theorem poly1305_almost_universal_msg' [Fact (Nat.Prime P)] (M M' : List UInt8)
    (hne : M ≠ M') :
    (Finset.univ.filter (fun r : ZMod P =>
      (msgPoly (blockNats (toBlocks M))).eval r
        = (msgPoly (blockNats (toBlocks M'))).eval r)).card
      ≤ max (blockNats (toBlocks M)).length (blockNats (toBlocks M')).length :=
  poly1305_almost_universal_msg M M' (fun h => hne (toBlockNats_inj M M'
    (by rw [← blockNats_toBlocks, ← blockNats_toBlocks]; exact h)))

end Poly1305.Spec
