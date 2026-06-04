import LeanChachaPoly.Poly1305.Spec

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

/-- A full block's value is less than 2¹²⁹. -/
theorem blockToNat_lt (block : List UInt8) (h : block.length = 16) :
    blockToNat block h < 2^129 := by
  simp [blockToNat, leToNat16]
  omega

/-! ## Block count -/

/-- Number of blocks equals ceiling of (msg.length / 16). -/
theorem toBlocks_length (msg : List UInt8) (hne : msg ≠ []) :
    (toBlocks msg).length = (msg.length + 15) / 16 := by
  induction msg using List.rec_on with
  | nil => contradiction
  | cons h t _ =>
    sorry

/-- Empty message gives empty block list. -/
@[simp]
theorem toBlocks_nil : toBlocks [] = [] := by
  simp [toBlocks, toBlocks.go]

/-! ## Structural: toBlocks on append -/

/-- When the first part is a multiple of 16 bytes, blocks split
    along the boundary. Used for streaming compositionality. -/
theorem toBlocks_append_aligned (xs ys : List UInt8)
    (h : xs.length % 16 = 0) :
    toBlocks (xs ++ ys) = toBlocks xs ++ toBlocks ys := by
  sorry

end Poly1305.Spec
