import LeanChachaPoly.Poly1305.Spec
import Mathlib

/-!
# Poly1305 Message Blocking Properties

Properties of `toBlocks`/`toBlockNats`: the functions that split a message into
16-byte chunks. `toBlocks` returns typed blocks (`List Block × Option FinalBlock`);
`toBlockNats` is the numeric (`List Nat`) engine the proofs induct over, tied to
`toBlocks` by `blockNats_toBlocks`.

## Key properties needed

1. Each full block has its 129th bit set (`blockToNat` adds 2¹²⁸)
2. The final partial block has its (8·length)th bit set
3. `toBlocks` terminates and covers the entire input
4. Number of blocks = ⌈msg.length / 16⌉
-/

namespace Poly1305.Spec

/-! ## blockToNat bounds -/

/-- A full block's value is at least 2¹²⁸ (the high bit is set). -/
theorem blockToNat_ge (block : Block) : 2 ^ 128 ≤ blockToNat block := by
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
theorem blockToNat_lt (block : Block) : blockToNat block < 2 ^ 129 := by
  have key : leToNat16 block < 2 ^ 128 := by
    unfold leToNat16
    rw [foldl_add_eq_sum, Nat.zero_add]
    have hbound : (List.map
          (fun i => (block.val.get (i.cast block.property.symm)).toNat * 2 ^ (i.val * 8))
          (List.finRange 16)).sum
        ≤ (List.map (fun i : Fin 16 => 255 * 2 ^ (i.val * 8)) (List.finRange 16)).sum := by
      apply List.sum_le_sum
      intro i _
      have hb : (block.val.get (i.cast block.property.symm)).toNat ≤ 255 := by
        have := (block.val.get (i.cast block.property.symm)).toNat_lt; omega
      exact Nat.mul_le_mul_right _ hb
    have hconst : (List.map (fun i : Fin 16 => 255 * 2 ^ (i.val * 8)) (List.finRange 16)).sum
        < 2 ^ 128 := by decide
    omega
  unfold blockToNat; omega

/-! ## Unfolding helpers -/

/-- One-step unfolding of `toBlockNats.go` on a non-empty list. The catch-all
    `| bs =>` match can't reduce on a variable, so we destructure to a `cons`. -/
theorem go_cons (bs : List UInt8) (hne : bs ≠ []) :
    toBlockNats.go bs =
      if h : (bs.take 16).length = 16 then
        blockToNat ⟨bs.take 16, h⟩ :: toBlockNats.go (bs.drop 16)
      else [finalBlockToNat ⟨bs.take 16, List.length_take_le 16 bs⟩] := by
  obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [toBlockNats.go]; exact hne

/-- One-step unfolding of the typed `toBlocks.go` on a non-empty list. -/
theorem toBlocks_go_cons (bs : List UInt8) (hne : bs ≠ []) :
    toBlocks.go bs =
      if h : (bs.take 16).length = 16 then
        (⟨bs.take 16, h⟩ :: (toBlocks.go (bs.drop 16)).1, (toBlocks.go (bs.drop 16)).2)
      else ([], some ⟨bs.take 16, List.length_take_le 16 bs⟩) := by
  obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [toBlocks.go]; exact hne

/-- `blockToNat` depends only on the block's bytes. -/
theorem blockToNat_congr {b1 b2 : Block} (e : b1.val = b2.val) :
    blockToNat b1 = blockToNat b2 := congrArg blockToNat (Subtype.ext e)

/-- Empty message gives empty block list. -/
@[simp]
theorem toBlockNats_nil : toBlockNats [] = [] := by
  simp [toBlockNats, toBlockNats.go]

/-- `blockNats (toBlocks ·)` equals the numeric engine `toBlockNats`. -/
theorem blockNats_toBlocks (msg : List UInt8) :
    blockNats (toBlocks msg) = toBlockNats msg := by
  show blockNats (toBlocks.go msg) = toBlockNats.go msg
  induction msg using toBlockNats.go.induct with
  | case1 => simp [toBlocks.go, toBlockNats.go, blockNats]
  | case2 bs hne _block _rest hlen ih =>
    rw [go_cons bs hne, dif_pos hlen, toBlocks_go_cons bs hne, dif_pos hlen,
      blockNats, List.map_cons, List.cons_append, ← blockNats, ih]
  | case3 bs hne _block hlen =>
    rw [go_cons bs hne, dif_neg hlen, toBlocks_go_cons bs hne, dif_neg hlen]
    simp [blockNats]

/-! ## Block count -/

private theorem goLen (bs : List UInt8) :
    (toBlockNats.go bs).length = (bs.length + 15) / 16 := by
  induction bs using toBlockNats.go.induct with
  | case1 => simp [toBlockNats.go]
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
theorem toBlockNats_length (msg : List UInt8) (_hne : msg ≠ []) :
    (toBlockNats msg).length = (msg.length + 15) / 16 := goLen msg

/-! ## Structural: toBlockNats on append -/

private theorem goAppend (ys xs : List UInt8) (h0 : xs.length % 16 = 0) :
    toBlockNats.go (xs ++ ys) = toBlockNats.go xs ++ toBlockNats.go ys := by
  induction xs using toBlockNats.go.induct with
  | case1 => simp [toBlockNats.go]
  | case2 xs hne _block rest hlen ih =>
    have hrest : rest = xs.drop 16 := rfl
    have hge : 16 ≤ xs.length := by have := hlen; rw [List.length_take] at this; omega
    have hxy : xs ++ ys ≠ [] := fun e => hne (List.append_eq_nil_iff.mp e).1
    have htk : (xs ++ ys).take 16 = xs.take 16 := List.take_append_of_le_length hge
    have hdp : (xs ++ ys).drop 16 = xs.drop 16 ++ ys := List.drop_append_of_le_length hge
    have h' : ((xs ++ ys).take 16).length = 16 := by rw [htk]; exact hlen
    rw [go_cons (xs ++ ys) hxy, dif_pos h', go_cons xs hne, dif_pos hlen, hdp]
    rw [hrest] at ih
    rw [ih (by rw [List.length_drop]; omega),
      blockToNat_congr (b1 := ⟨(xs ++ ys).take 16, h'⟩) (b2 := ⟨xs.take 16, hlen⟩) htk,
      List.cons_append]
  | case3 xs hne _block hlen =>
    exfalso
    have hh := hlen; rw [List.length_take] at hh
    have hpos : xs.length ≠ 0 := fun e => hne (List.length_eq_zero_iff.mp e)
    omega

/-- When the first part is a multiple of 16 bytes, blocks split along the
    boundary. The compositionality property a streaming MAC would rely on. -/
theorem toBlockNats_append_aligned (xs ys : List UInt8)
    (h : xs.length % 16 = 0) :
    toBlockNats (xs ++ ys) = toBlockNats xs ++ toBlockNats ys := goAppend ys xs h

end Poly1305.Spec
