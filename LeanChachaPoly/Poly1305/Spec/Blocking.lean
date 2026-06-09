import LeanChachaPoly.Poly1305.Spec
import LeanChachaPoly.Poly1305.Spec.Sum
import Mathlib

/-!
# Poly1305 Message Blocking Properties

Block-value bounds and the `toBlocks` / `toBlockNats` correspondence. `toBlocks`
returns typed blocks (`List Block × Option FinalBlock`); `toBlockNats` is the numeric
(`List Nat`) engine the injectivity/security proofs induct over, and the two agree by
`blockNats_toBlocks`. A full block carries the `2¹²⁸` high bit (so its value lies in
`[2¹²⁸, 2¹²⁹)`); the final partial block carries a `2^(8·len)` bit instead.
-/

namespace Poly1305.Spec

/-! ## blockToNat bounds -/

/-- **Supporting.** A full block's value is at least 2¹²⁸ (the high bit is set). -/
theorem blockToNat_ge (block : Block) : 2 ^ 128 ≤ blockToNat block := by
  simp [blockToNat]

/-- **Supporting.** A full block's value is less than 2¹²⁹ (the 16 little-endian bytes
    sum to
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

end Poly1305.Spec
