import LeanChachaPoly.ChaCha20.Spec

/-!
# Poly1305 MAC — Specification

RFC 8439 §2.5. A one-time message authentication code based on
polynomial evaluation in GF(2¹³⁰ - 5).

## Why Poly1305 is good for verification

- The mathematics is modular arithmetic over a specific prime — no
  field inversions, no elliptic curves.
- The key lemma (accumulation = polynomial evaluation) is a clean
  induction. Each step involves one multiply and one add mod P.
- `omega` handles most arithmetic bounds once you unfold the
  definitions; the modular reasoning is mechanical.

## Module structure

  Poly1305.Spec            ← this file: types, definitions, capstones
  Poly1305.Spec.Blocking   ← message-blocking properties
  Poly1305.Spec.Accumulate ← accumulation = polynomial evaluation
  Poly1305.Native          ← ByteArray bridge
-/
namespace Poly1305.Spec

/-! ## Constants -/

/-- 2¹³⁰ - 5. The largest prime below 2¹³⁰. -/
def P : Nat := 2^130 - 5

theorem P_pos : 0 < P := by native_decide

/-! ## Key structure (RFC 8439 §2.5.1) -/

/-- A 256-bit Poly1305 key: first 16 bytes are `r` (clamped),
    last 16 bytes are `s`. -/
structure Key where
  bytes : List UInt8
  size  : bytes.length = 32

/-- Deserialize 16 bytes as a little-endian `Nat`. -/
def leToNat16 (bs : List UInt8) (h : bs.length = 16) : Nat :=
  (List.finRange 16).foldl (fun acc i =>
    acc + (bs.get (i.cast h.symm)).toNat * 2^(i.val * 8)) 0

/-- Clamp `r`: clear specific bits per RFC 8439 §2.5.1.
    Clamping ensures certain bits of r are zero, which prevents
    timing attacks and simplifies reduction. -/
def clamp (r : Nat) : Nat :=
  r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- Extract and clamp `r` from the key. -/
def extractR (key : Key) : Nat :=
  clamp (leToNat16 (key.bytes.take 16) (by simp [key.size]))

/-- Extract `s` from the key. -/
def extractS (key : Key) : Nat :=
  leToNat16 (key.bytes.drop 16)
    (by simp [List.length_drop, key.size])

/-! ## Message blocking (RFC 8439 §2.5.1) -/

/-- Convert a complete 16-byte block to a Nat with a high bit set. -/
def blockToNat (block : List UInt8) (h : block.length = 16) : Nat :=
  leToNat16 block h + 2^128

/-- The last (possibly partial) block: also gets a high bit but
    at position `block.length * 8`, not 128. -/
def finalBlockToNat (block : List UInt8) (h : block.length ≤ 16) : Nat :=
  (List.finRange block.length).foldl (fun acc i =>
    acc + (block.get i).toNat * 2^(i.val * 8)) 0
  + 2^(block.length * 8)

/-- Split a message into 16-byte blocks, converted to Nat values. -/
def toBlocks (msg : List UInt8) : List Nat :=
  go msg
where
  go : List UInt8 → List Nat
    | [] => []
    | bs =>
      let block := bs.take 16
      let rest  := bs.drop 16
      if h : block.length = 16 then
        blockToNat block h :: go rest
      else
        [finalBlockToNat block (by
          have : block.length ≤ 16 := by
            simp only [block, List.length_take]
            exact Nat.min_le_left _ _
          omega)]
  termination_by bs => bs.length
  decreasing_by
    simp only [rest, List.length_drop]
    have hlen : bs.length ≥ 16 := by
      have htake := @List.length_take UInt8 16 bs
      simp only [block] at h
      omega
    omega

/-! ## Accumulation (RFC 8439 §2.5.1) -/

/-- Process one block: `acc = ((acc + block) * r) % P`. -/
def step (r : Nat) (acc block : Nat) : Nat :=
  ((acc + block) * r) % P

/-- Accumulate all blocks. -/
def accumulate (r : Nat) (blocks : List Nat) : Nat :=
  blocks.foldl (step r) 0

/-! ## Serialization -/

/-- Pack a 128-bit (16-byte) Nat as little-endian bytes. -/
def natToLe16 (n : Nat) : List UInt8 :=
  (List.range 16).map fun i => UInt8.ofNat ((n >>> (i * 8)) % 256)

/-! ## Full MAC -/

/-- Compute the Poly1305 tag.
    Result: `(accumulate(r, blocks) + s) mod 2¹²⁸` as 16 bytes. -/
def poly1305 (key : Key) (msg : List UInt8) : List UInt8 :=
  let r      := extractR key
  let s      := extractS key
  let blocks := toBlocks msg
  let acc    := accumulate r blocks
  natToLe16 ((acc + s) % 2^128)


/-! ================================================================
    CAPSTONE THEOREMS
    ================================================================ -/

/-! ### P1: Tag length -/
theorem poly1305_length (key : Key) (msg : List UInt8) :
    (poly1305 key msg).length = 16 := by
  simp [poly1305, natToLe16, List.length_map]

/-! ### P2: accumulate stays in field -/
theorem step_lt_P (r acc block : Nat) : step r acc block < P := by
  simp [step, P]
  exact Nat.mod_lt _ (by native_decide)

theorem accumulate_lt_P (r : Nat) (blocks : List Nat) :
    accumulate r blocks < P := by
  unfold accumulate
  suffices h : ∀ acc, acc < P → blocks.foldl (step r) acc < P from
    h 0 P_pos
  intro acc hacc
  induction blocks generalizing acc with
  | nil => simpa
  | cons block rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (step_lt_P r acc block)

/-! ### P3: Accumulation over append (streaming compositionality) -/
theorem accumulate_append (r : Nat) (xs ys : List Nat) :
    accumulate r (xs ++ ys) =
      ys.foldl (step r) (accumulate r xs) := by
  simp [accumulate, List.foldl_append]

/-! ### P4: Empty message tag -/
theorem poly1305_empty (key : Key) :
    poly1305 key [] =
      natToLe16 (extractS key % 2^128) := by
  have h : toBlocks [] = [] := by native_decide
  simp [poly1305, h, accumulate]

/-! ### P5: Clamped r is bounded -/
theorem clamp_lt (r : Nat) : clamp r < 2^128 := by
  unfold clamp
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by native_decide)

end Poly1305.Spec
