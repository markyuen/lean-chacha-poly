import LeanChachaPoly.Fast.Types

/-!
# Poly1305 — fast implementation

Two engines over `ByteArray` messages with offset-indexed block loads:

- `accumulate` — the production path: poly1305-donna-style 5×26-bit limb
  arithmetic in unboxed `UInt64` (zero heap allocation per block; the only
  GMP work is once per message: the `r` limb split, the freeze, and the
  optional trailing partial block).
- `accumulateNat` — the Phase A baseline: one GMP `Spec.step` (130-bit
  mul + mod) per block. Retained with its own equivalence theorem
  (`accumulateNat_eq`, and `accumulate_eq_accumulateNat` tying the two
  engines together) plus differential tests and a benchmark row.

Everything is written with `+ * / %` and power-of-two literals rather than
bitwise ops: clang compiles unsigned div/mod by constant powers of two to
shifts/ands, and the all-arithmetic form keeps the bridge proofs inside
`omega`'s fragment.

Equivalence with `Poly1305.Spec.poly1305` is proved in
`LeanChachaPoly.Fast.Bridge.Poly1305` (`poly1305_eq_spec`).

This file is Mathlib-free; it is linked into the `test` and `bench`
executables.
-/

namespace Poly1305.Fast

open Poly1305.Spec (P clamp step)

/-! ## Little-endian loads -/

/-- Load 8 bytes at offset `off` as a little-endian `UInt64`. -/
@[inline] def load8 (m : ByteArray) (off : Nat) (h : off + 8 ≤ m.size) : UInt64 :=
  (m[off]'(by omega)).toUInt64
  + (m[off + 1]'(by omega)).toUInt64 * 256
  + (m[off + 2]'(by omega)).toUInt64 * 65536
  + (m[off + 3]'(by omega)).toUInt64 * 16777216
  + (m[off + 4]'(by omega)).toUInt64 * 4294967296
  + (m[off + 5]'(by omega)).toUInt64 * 1099511627776
  + (m[off + 6]'(by omega)).toUInt64 * 281474976710656
  + (m[off + 7]'(by omega)).toUInt64 * 72057594037927936

/-- Load 16 bytes at offset `off` as a little-endian `Nat` (< 2¹²⁸). -/
@[inline] def load16 (m : ByteArray) (off : Nat) (h : off + 16 ≤ m.size) : Nat :=
  (load8 m off (by omega)).toNat + (load8 m (off + 8) (by omega)).toNat * 2^64

/-- Load the trailing bytes `[off, m.size)` as a little-endian `Nat` and add
    the `2^(len·8)` high bit — the fast `finalBlockToNat`. -/
def loadFinal (m : ByteArray) (off : Nat) : Nat :=
  go off 0 0 + 2^((m.size - off) * 8)
where
  go (j : Nat) (shift : Nat) (acc : Nat) : Nat :=
    if h : j < m.size then
      go (j + 1) (shift + 8) (acc + (m[j]'h).toNat * 2^shift)
    else acc
  termination_by m.size - j

/-! ## Key extraction (RFC 8439 §2.5.1) -/

/-- Extract and clamp `r` (first 16 bytes of the key). -/
def extractR (key : Key) : Nat :=
  clamp (load16 key.val 0 (by rw [key.property]; omega))

/-- Extract `s` (last 16 bytes of the key). -/
def extractS (key : Key) : Nat :=
  load16 key.val 16 (by rw [key.property]; omega)

/-! ## Accumulation -/

/-- The Nat-engine accumulation (Phase A): full 16-byte blocks get the `2¹²⁸`
    high bit, a trailing partial block gets `2^(len·8)`; every block takes one
    GMP `Spec.step`. Superseded by the limb-engine `accumulate` below; kept as
    the differential-test and benchmark baseline. -/
def accumulateNat (r : Nat) (m : ByteArray) : Nat :=
  go 0 0
where
  go (off acc : Nat) : Nat :=
    if h : off + 16 ≤ m.size then
      go (off + 16) (step r acc (load16 m off h + 2^128))
    else if off < m.size then
      step r acc (loadFinal m off)
    else acc
  termination_by m.size - off

/-! ## Limb accumulation (poly1305-donna style, 5×26-bit limbs)

The per-block work is pure unboxed `UInt64` arithmetic — no `Nat` allocation
until the final freeze. Written with `+ * / %` and power-of-two literals only
(no bitwise ops): clang compiles unsigned div/mod by constant powers of two to
shifts/ands, and the all-arithmetic form keeps the bridge proofs in `omega`'s
fragment. The accumulator rides in five 26-bit limbs `h0..h4` (radix 2²⁶) with
the invariant `hᵢ < 2²⁷`; `r` is preloaded as limbs `r0..r4 < 2²⁶` plus
`s1..s4 = 5·r1..5·r4` so the `2¹³⁰ ≡ 5 (mod P)` wrap folds into the schoolbook
products, which then fit `UInt64` (each `dᵢ < 2⁶⁰`). One carry pass plus the
mandatory extra `g0 → h1` carry restores the invariant. -/

/-- Value of a 5×26-bit limb accumulator. -/
def limbsToNat (h0 h1 h2 h3 h4 : UInt64) : Nat :=
  h0.toNat + h1.toNat * 2^26 + h2.toNat * 2^52 + h3.toNat * 2^78 + h4.toNat * 2^104

/-- Accumulate all blocks with limb arithmetic. Full 16-byte blocks run on the
    `UInt64` limb engine; the optional trailing partial block takes one
    `Spec.step` on the frozen value (one GMP multiply per message). The `r % P`
    reduction makes the result agree with the spec's `accumulate` for *every*
    `r`, and is an identity for real (clamped, < 2¹²⁸) keys. -/
def accumulate (r : Nat) (m : ByteArray) : Nat :=
  let rr := r % P
  go (UInt64.ofNat (rr % 67108864))
     (UInt64.ofNat (rr / 67108864 % 67108864))
     (UInt64.ofNat (rr / 4503599627370496 % 67108864))
     (UInt64.ofNat (rr / 302231454903657293676544 % 67108864))
     (UInt64.ofNat (rr / 20282409603651670423947251286016))
     (UInt64.ofNat (5 * (rr / 67108864 % 67108864)))
     (UInt64.ofNat (5 * (rr / 4503599627370496 % 67108864)))
     (UInt64.ofNat (5 * (rr / 302231454903657293676544 % 67108864)))
     (UInt64.ofNat (5 * (rr / 20282409603651670423947251286016)))
     0 0 0 0 0 0
where
  go (r0 r1 r2 r3 r4 s1 s2 s3 s4 : UInt64) (off : Nat) (h0 h1 h2 h3 h4 : UInt64) : Nat :=
    if h : off + 16 ≤ m.size then
      let lo := load8 m off (by omega)
      let hi := load8 m (off + 8) (by omega)
      -- block limbs folded into the accumulator (2^24 = the full-block high bit)
      let u0 := h0 + lo % 67108864
      let u1 := h1 + lo / 67108864 % 67108864
      let u2 := h2 + (lo / 4503599627370496 + hi % 16384 * 4096)
      let u3 := h3 + hi / 16384 % 67108864
      let u4 := h4 + (hi / 1099511627776 + 16777216)
      -- schoolbook multiply with the 2^130 ≡ 5 wrap folded in via s_i = 5·r_i
      let d0 := u0 * r0 + u1 * s4 + u2 * s3 + u3 * s2 + u4 * s1
      let d1 := u0 * r1 + u1 * r0 + u2 * s4 + u3 * s3 + u4 * s2
      let d2 := u0 * r2 + u1 * r1 + u2 * r0 + u3 * s4 + u4 * s3
      let d3 := u0 * r3 + u1 * r2 + u2 * r1 + u3 * r0 + u4 * s4
      let d4 := u0 * r4 + u1 * r3 + u2 * r2 + u3 * r1 + u4 * r0
      -- carry chain, top wrap (·5), and the extra g0 → h1 carry
      let e1 := d1 + d0 / 67108864
      let e2 := d2 + e1 / 67108864
      let e3 := d3 + e2 / 67108864
      let e4 := d4 + e3 / 67108864
      let g0 := d0 % 67108864 + e4 / 67108864 * 5
      go r0 r1 r2 r3 r4 s1 s2 s3 s4 (off + 16)
        (g0 % 67108864) (e1 % 67108864 + g0 / 67108864)
        (e2 % 67108864) (e3 % 67108864) (e4 % 67108864)
    else
      let acc := limbsToNat h0 h1 h2 h3 h4 % P
      if off < m.size then step r acc (loadFinal m off) else acc
  termination_by m.size - off

/-! ## Tag serialization -/

/-- Push a 128-bit `Nat` as 16 little-endian bytes — the fast `natToLe16`,
    unrolled. -/
def pushTag (acc : ByteArray) (n : Nat) : ByteArray :=
  let byte (i : Nat) : UInt8 := UInt8.ofNat ((n >>> (i * 8)) % 256)
  let acc := (((acc.push (byte 0)).push (byte 1)).push (byte 2)).push (byte 3)
  let acc := (((acc.push (byte 4)).push (byte 5)).push (byte 6)).push (byte 7)
  let acc := (((acc.push (byte 8)).push (byte 9)).push (byte 10)).push (byte 11)
  (((acc.push (byte 12)).push (byte 13)).push (byte 14)).push (byte 15)

/-! ## Full MAC -/

/-- Compute the Poly1305 tag: `(accumulate(r, m) + s) mod 2¹²⁸` as 16
    little-endian bytes. -/
def poly1305 (key : Key) (msg : ByteArray) : ByteArray :=
  let r := extractR key
  let s := extractS key
  pushTag (ByteArray.emptyWithCapacity 16) ((accumulate r msg + s) % 2^128)

end Poly1305.Fast
