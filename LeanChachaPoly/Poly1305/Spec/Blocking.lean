import LeanChachaPoly.Poly1305.Spec
import Mathlib

/-!
# Poly1305 Message Blocking Properties

Properties of `toBlocks`: the function that splits a message into
16-byte chunks and converts each to a Nat.

## Key properties needed

1. Each full block has its 129th bit set (`blockToNat` adds 2¹²⁸)
2. The final partial block has its (8·length)th bit set
3. `toBlocks` terminates and covers the entire input
4. Number of blocks = ⌈msg.length / 16⌉
-/

namespace Poly1305.Spec

/-! ## blockToNat bounds -/

/-- A full block's value is at least 2¹²⁸ (the high bit is set). -/
theorem blockToNat_ge (block : List UInt8) (h : block.length = 16) :
    2^128 ≤ blockToNat block h := by
  simp [blockToNat]

/-- Folding `(acc + g i)` over a list is the running sum. -/
private theorem foldl_add_eq_sum {α : Type} (l : List α) (g : α → Nat) (init : Nat) :
    l.foldl (fun acc i => acc + g i) init = init + (l.map g).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih => simp [ih]; ring

/-- A full block's value is less than 2¹²⁹ (the 16 little-endian bytes sum to
    `< 2¹²⁸`, plus the `2¹²⁸` high bit). Each positional term is `≤ 255·2^(8i)`,
    and the geometric sum is `2¹²⁸ − 1`. -/
theorem blockToNat_lt (block : List UInt8) (h : block.length = 16) :
    blockToNat block h < 2 ^ 129 := by
  have key : leToNat16 block h < 2 ^ 128 := by
    unfold leToNat16
    rw [foldl_add_eq_sum, Nat.zero_add]
    have hbound : (List.map (fun i => (block.get (i.cast h.symm)).toNat * 2 ^ (i.val * 8))
        (List.finRange 16)).sum
        ≤ (List.map (fun i : Fin 16 => 255 * 2 ^ (i.val * 8)) (List.finRange 16)).sum := by
      apply List.sum_le_sum
      intro i _
      have hb : (block.get (i.cast h.symm)).toNat ≤ 255 := by
        have := (block.get (i.cast h.symm)).toNat_lt; omega
      exact Nat.mul_le_mul_right _ hb
    have hconst : (List.map (fun i : Fin 16 => 255 * 2 ^ (i.val * 8)) (List.finRange 16)).sum
        < 2 ^ 128 := by native_decide
    omega
  unfold blockToNat; omega

/-! ## Unfolding helpers -/

/-- One-step unfolding of `toBlocks.go` on a non-empty list. The catch-all
    `| bs =>` match can't reduce on a variable, so we destructure to a `cons`. -/
theorem go_cons (bs : List UInt8) (hne : bs ≠ []) :
    toBlocks.go bs =
      if h : (bs.take 16).length = 16 then
        blockToNat (bs.take 16) h :: toBlocks.go (bs.drop 16)
      else [finalBlockToNat (bs.take 16) (List.length_take_le 16 bs)] := by
  obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [toBlocks.go]; exact hne

/-- `blockToNat` depends only on the block's bytes, not the length proof. -/
theorem blockToNat_congr {b1 b2 : List UInt8} (h1 : b1.length = 16) (h2 : b2.length = 16)
    (e : b1 = b2) : blockToNat b1 h1 = blockToNat b2 h2 := by subst e; rfl

/-- Empty message gives empty block list. -/
@[simp]
theorem toBlocks_nil : toBlocks [] = [] := by
  simp [toBlocks, toBlocks.go]

/-! ## Block count -/

private theorem goLen (bs : List UInt8) :
    (toBlocks.go bs).length = (bs.length + 15) / 16 := by
  induction bs using toBlocks.go.induct with
  | case1 => simp [toBlocks.go]
  | case2 bs hne _block _rest hlen ih =>
    rw [go_cons bs hne, dif_pos hlen, List.length_cons, ih, List.length_drop]
    have hh := hlen; rw [List.length_take] at hh
    omega
  | case3 bs hne _block hlen =>
    rw [go_cons bs hne, dif_neg hlen]
    have hh := hlen; rw [List.length_take] at hh
    have hpos : bs.length ≠ 0 := fun e => hne (List.length_eq_zero_iff.mp e)
    simp only [List.length_cons, List.length_nil]
    omega

/-- Number of blocks equals ⌈msg.length / 16⌉. -/
theorem toBlocks_length (msg : List UInt8) (_hne : msg ≠ []) :
    (toBlocks msg).length = (msg.length + 15) / 16 := goLen msg

/-! ## Structural: toBlocks on append -/

private theorem goAppend (ys xs : List UInt8) (h0 : xs.length % 16 = 0) :
    toBlocks.go (xs ++ ys) = toBlocks.go xs ++ toBlocks.go ys := by
  induction xs using toBlocks.go.induct with
  | case1 => simp [toBlocks.go]
  | case2 xs hne _block rest hlen ih =>
    have hrest : rest = xs.drop 16 := rfl
    have hge : 16 ≤ xs.length := by have := hlen; rw [List.length_take] at this; omega
    have hxy : xs ++ ys ≠ [] := fun e => hne (List.append_eq_nil_iff.mp e).1
    have htk : (xs ++ ys).take 16 = xs.take 16 := List.take_append_of_le_length hge
    have hdp : (xs ++ ys).drop 16 = xs.drop 16 ++ ys := List.drop_append_of_le_length hge
    have h' : ((xs ++ ys).take 16).length = 16 := by rw [htk]; exact hlen
    rw [go_cons (xs ++ ys) hxy, dif_pos h', go_cons xs hne, dif_pos hlen, hdp]
    rw [hrest] at ih
    rw [ih (by rw [List.length_drop]; omega), blockToNat_congr h' hlen htk, List.cons_append]
  | case3 xs hne _block hlen =>
    exfalso
    have hh := hlen; rw [List.length_take] at hh
    have hpos : xs.length ≠ 0 := fun e => hne (List.length_eq_zero_iff.mp e)
    omega

/-- When the first part is a multiple of 16 bytes, blocks split along the
    boundary. The compositionality property a streaming MAC would rely on. -/
theorem toBlocks_append_aligned (xs ys : List UInt8)
    (h : xs.length % 16 = 0) :
    toBlocks (xs ++ ys) = toBlocks xs ++ toBlocks ys := goAppend ys xs h

end Poly1305.Spec
