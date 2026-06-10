import LeanChachaPoly.Fast.Poly1305
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Basic

/-!
# Fast bridge — Poly1305 limb step

The per-block correctness of the 5×26-bit limb engine: one `accumulateLimb.go`
iteration multiplies the accumulator-plus-block by `r` modulo `P = 2¹³⁰ − 5`
and restores the limb invariant (`stepLimbs`). The loop-level bridge to the
spec's `accumulate` lives in `Fast.Bridge.Poly1305`.

Proof shape: every `UInt64` operation is transported to `Nat` by the
`UInt64.toNat_*` lemmas; the limb bounds make all the `% 2⁶⁴` reductions
vanish by `omega`. The two non-linear facts are isolated: the 5×5 schoolbook
product with the `5·rⱼ` wrap terms is a `ring` identity (`mul_wrap`), and the
carry chain is a value-preserving `omega` identity (`carry_fixup`). Everything
else is linear arithmetic over the product atoms.

`stepLimbs` takes its intermediates (`u`, `d`, `e`, `g0`) as *equation
hypotheses* (`hu0 : u0 = h0 + lo % 67108864`, …) so the caller discharges them
with `rfl` against the zeta-expanded body of `accumulateLimb.go`.
-/

namespace Poly1305.Fast

private theorem P_eq :
    Poly1305.Spec.P = 1361129467683753853853498429727072845819 := by
  norm_num [Poly1305.Spec.P]

/-- **Supporting.** The 5×5 schoolbook product with the `5·rⱼ` wrap terms:
    folding `2¹³⁰ ≡ 5` into the high partial products is exact up to an
    explicit multiple of `2¹³⁰ − 5`. -/
private theorem mul_wrap (u0 u1 u2 u3 u4 r0 r1 r2 r3 r4 : Nat) :
    (u0 + u1*2^26 + u2*2^52 + u3*2^78 + u4*2^104)
      * (r0 + r1*2^26 + r2*2^52 + r3*2^78 + r4*2^104)
    = (u0*r0 + u1*(5*r4) + u2*(5*r3) + u3*(5*r2) + u4*(5*r1))
    + (u0*r1 + u1*r0 + u2*(5*r4) + u3*(5*r3) + u4*(5*r2)) * 2^26
    + (u0*r2 + u1*r1 + u2*r0 + u3*(5*r4) + u4*(5*r3)) * 2^52
    + (u0*r3 + u1*r2 + u2*r1 + u3*r0 + u4*(5*r4)) * 2^78
    + (u0*r4 + u1*r3 + u2*r2 + u3*r1 + u4*r0) * 2^104
    + (u1*r4 + u2*r3 + u3*r2 + u4*r1
        + (u2*r4 + u3*r3 + u4*r2) * 2^26
        + (u3*r4 + u4*r3) * 2^52
        + u4*r4 * 2^78) * 1361129467683753853853498429727072845819 := by
  ring

/-- **Supporting.** The carry chain (with top wrap `·5` and the extra
    `g0 → h1` carry) preserves the value up to the multiple of `2¹³⁰ − 5`
    removed by the wrap. Pure div/mod algebra. -/
private theorem carry_fixup (x0 x1 x2 x3 x4 : Nat) :
    (x0 % 67108864 + (x4 + (x3 + (x2 + (x1 + x0 / 67108864) / 67108864) / 67108864) / 67108864) / 67108864 * 5) % 67108864
    + ((x1 + x0 / 67108864) % 67108864
        + (x0 % 67108864 + (x4 + (x3 + (x2 + (x1 + x0 / 67108864) / 67108864) / 67108864) / 67108864) / 67108864 * 5) / 67108864) * 2^26
    + ((x2 + (x1 + x0 / 67108864) / 67108864) % 67108864) * 2^52
    + ((x3 + (x2 + (x1 + x0 / 67108864) / 67108864) / 67108864) % 67108864) * 2^78
    + ((x4 + (x3 + (x2 + (x1 + x0 / 67108864) / 67108864) / 67108864) / 67108864) % 67108864) * 2^104
    + (x4 + (x3 + (x2 + (x1 + x0 / 67108864) / 67108864) / 67108864) / 67108864) / 67108864
        * 1361129467683753853853498429727072845819
    = x0 + x1 * 2^26 + x2 * 2^52 + x3 * 2^78 + x4 * 2^104 := by
  omega

/-- **Key lemma.** One limb-engine block step is multiplication by `r` mod
    `P`, and the output limbs satisfy the `< 2²⁷` invariant. The
    intermediates are equation hypotheses, discharged by `rfl` at the use
    site against the zeta-expanded `accumulateLimb.go` body. -/
theorem stepLimbs (r0 r1 r2 r3 r4 s1 s2 s3 s4 lo hi h0 h1 h2 h3 h4 : UInt64)
    (hr0 : r0.toNat < 2^26) (hr1 : r1.toNat < 2^26) (hr2 : r2.toNat < 2^26)
    (hr3 : r3.toNat < 2^26) (hr4 : r4.toNat < 2^26)
    (hs1 : s1.toNat = 5 * r1.toNat) (hs2 : s2.toNat = 5 * r2.toNat)
    (hs3 : s3.toNat = 5 * r3.toNat) (hs4 : s4.toNat = 5 * r4.toNat)
    (hw0 : h0.toNat < 2^27) (hw1 : h1.toNat < 2^27) (hw2 : h2.toNat < 2^27)
    (hw3 : h3.toNat < 2^27) (hw4 : h4.toNat < 2^27)
    (u0 u1 u2 u3 u4 d0 d1 d2 d3 d4 e1 e2 e3 e4 g0 : UInt64)
    (hu0 : u0 = h0 + lo % 67108864)
    (hu1 : u1 = h1 + lo / 67108864 % 67108864)
    (hu2 : u2 = h2 + (lo / 4503599627370496 + hi % 16384 * 4096))
    (hu3 : u3 = h3 + hi / 16384 % 67108864)
    (hu4 : u4 = h4 + (hi / 1099511627776 + 16777216))
    (hd0 : d0 = u0 * r0 + u1 * s4 + u2 * s3 + u3 * s2 + u4 * s1)
    (hd1 : d1 = u0 * r1 + u1 * r0 + u2 * s4 + u3 * s3 + u4 * s2)
    (hd2 : d2 = u0 * r2 + u1 * r1 + u2 * r0 + u3 * s4 + u4 * s3)
    (hd3 : d3 = u0 * r3 + u1 * r2 + u2 * r1 + u3 * r0 + u4 * s4)
    (hd4 : d4 = u0 * r4 + u1 * r3 + u2 * r2 + u3 * r1 + u4 * r0)
    (he1 : e1 = d1 + d0 / 67108864) (he2 : e2 = d2 + e1 / 67108864)
    (he3 : e3 = d3 + e2 / 67108864) (he4 : e4 = d4 + e3 / 67108864)
    (hg0 : g0 = d0 % 67108864 + e4 / 67108864 * 5) :
    limbsToNat (g0 % 67108864) (e1 % 67108864 + g0 / 67108864)
        (e2 % 67108864) (e3 % 67108864) (e4 % 67108864) % Poly1305.Spec.P
      = ((limbsToNat h0 h1 h2 h3 h4 + (lo.toNat + hi.toNat * 2^64 + 2^128))
          * (r0.toNat + r1.toNat*2^26 + r2.toNat*2^52 + r3.toNat*2^78 + r4.toNat*2^104))
        % Poly1305.Spec.P
    ∧ (g0 % 67108864).toNat < 2^27
    ∧ (e1 % 67108864 + g0 / 67108864).toNat < 2^27
    ∧ (e2 % 67108864).toNat < 2^27
    ∧ (e3 % 67108864).toNat < 2^27
    ∧ (e4 % 67108864).toNat < 2^27 := by
  have hlo := lo.toNat_lt
  have hhi := hi.toNat_lt
  -- s bounds
  have hsb1 : s1.toNat < 2^29 := by omega
  have hsb2 : s2.toNat < 2^29 := by omega
  have hsb3 : s3.toNat < 2^29 := by omega
  have hsb4 : s4.toNat < 2^29 := by omega
  -- u transports (exact Nat values; the additions cannot wrap)
  have hu0' : u0.toNat = h0.toNat + lo.toNat % 67108864 := by
    subst hu0
    simp only [UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow]
    omega
  have hu1' : u1.toNat = h1.toNat + lo.toNat / 67108864 % 67108864 := by
    subst hu1
    simp only [UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_div,
      UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    omega
  have hu2' : u2.toNat = h2.toNat + (lo.toNat / 4503599627370496 + hi.toNat % 16384 * 4096) := by
    subst hu2
    simp only [UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_div,
      UInt64.toNat_mul, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    omega
  have hu3' : u3.toNat = h3.toNat + hi.toNat / 16384 % 67108864 := by
    subst hu3
    simp only [UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_div,
      UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    omega
  have hu4' : u4.toNat = h4.toNat + (hi.toNat / 1099511627776 + 16777216) := by
    subst hu4
    simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow]
    omega
  -- u bounds
  have hub0 : u0.toNat < 2^28 := by omega
  have hub1 : u1.toNat < 2^28 := by omega
  have hub2 : u2.toNat < 2^28 := by omega
  have hub3 : u3.toNat < 2^28 := by omega
  have hub4 : u4.toNat < 2^28 := by omega
  -- d transports: per-product bounds (explicit-product RHS for unification),
  -- then the five-product sums stay below 2^64.
  have hd0' : d0.toNat = u0.toNat * r0.toNat + u1.toNat * s4.toNat
      + u2.toNat * s3.toNat + u3.toNat * s2.toNat + u4.toNat * s1.toNat := by
    subst hd0
    have p0 : u0.toNat * r0.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub0 hr0
    have p1 : u1.toNat * s4.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub1 hsb4
    have p2 : u2.toNat * s3.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub2 hsb3
    have p3 : u3.toNat * s2.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub3 hsb2
    have p4 : u4.toNat * s1.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub4 hsb1
    simp only [UInt64.toNat_add, UInt64.toNat_mul, Nat.reducePow]
    omega
  have hd1' : d1.toNat = u0.toNat * r1.toNat + u1.toNat * r0.toNat
      + u2.toNat * s4.toNat + u3.toNat * s3.toNat + u4.toNat * s2.toNat := by
    subst hd1
    have p0 : u0.toNat * r1.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub0 hr1
    have p1 : u1.toNat * r0.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub1 hr0
    have p2 : u2.toNat * s4.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub2 hsb4
    have p3 : u3.toNat * s3.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub3 hsb3
    have p4 : u4.toNat * s2.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub4 hsb2
    simp only [UInt64.toNat_add, UInt64.toNat_mul, Nat.reducePow]
    omega
  have hd2' : d2.toNat = u0.toNat * r2.toNat + u1.toNat * r1.toNat
      + u2.toNat * r0.toNat + u3.toNat * s4.toNat + u4.toNat * s3.toNat := by
    subst hd2
    have p0 : u0.toNat * r2.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub0 hr2
    have p1 : u1.toNat * r1.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub1 hr1
    have p2 : u2.toNat * r0.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub2 hr0
    have p3 : u3.toNat * s4.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub3 hsb4
    have p4 : u4.toNat * s3.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub4 hsb3
    simp only [UInt64.toNat_add, UInt64.toNat_mul, Nat.reducePow]
    omega
  have hd3' : d3.toNat = u0.toNat * r3.toNat + u1.toNat * r2.toNat
      + u2.toNat * r1.toNat + u3.toNat * r0.toNat + u4.toNat * s4.toNat := by
    subst hd3
    have p0 : u0.toNat * r3.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub0 hr3
    have p1 : u1.toNat * r2.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub1 hr2
    have p2 : u2.toNat * r1.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub2 hr1
    have p3 : u3.toNat * r0.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub3 hr0
    have p4 : u4.toNat * s4.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub4 hsb4
    simp only [UInt64.toNat_add, UInt64.toNat_mul, Nat.reducePow]
    omega
  have hd4' : d4.toNat = u0.toNat * r4.toNat + u1.toNat * r3.toNat
      + u2.toNat * r2.toNat + u3.toNat * r1.toNat + u4.toNat * r0.toNat := by
    subst hd4
    have p0 : u0.toNat * r4.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub0 hr4
    have p1 : u1.toNat * r3.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub1 hr3
    have p2 : u2.toNat * r2.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub2 hr2
    have p3 : u3.toNat * r1.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub3 hr1
    have p4 : u4.toNat * r0.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub4 hr0
    simp only [UInt64.toNat_add, UInt64.toNat_mul, Nat.reducePow]
    omega
  -- d bounds (products bounded again, this time for the carry transports)
  have hdb0 : d0.toNat < 2^60 := by
    have p0 : u0.toNat * r0.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub0 hr0
    have p1 : u1.toNat * s4.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub1 hsb4
    have p2 : u2.toNat * s3.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub2 hsb3
    have p3 : u3.toNat * s2.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub3 hsb2
    have p4 : u4.toNat * s1.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub4 hsb1
    omega
  have hdb1 : d1.toNat < 2^60 := by
    have p0 : u0.toNat * r1.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub0 hr1
    have p1 : u1.toNat * r0.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub1 hr0
    have p2 : u2.toNat * s4.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub2 hsb4
    have p3 : u3.toNat * s3.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub3 hsb3
    have p4 : u4.toNat * s2.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub4 hsb2
    omega
  have hdb2 : d2.toNat < 2^60 := by
    have p0 : u0.toNat * r2.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub0 hr2
    have p1 : u1.toNat * r1.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub1 hr1
    have p2 : u2.toNat * r0.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub2 hr0
    have p3 : u3.toNat * s4.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub3 hsb4
    have p4 : u4.toNat * s3.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub4 hsb3
    omega
  have hdb3 : d3.toNat < 2^60 := by
    have p0 : u0.toNat * r3.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub0 hr3
    have p1 : u1.toNat * r2.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub1 hr2
    have p2 : u2.toNat * r1.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub2 hr1
    have p3 : u3.toNat * r0.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub3 hr0
    have p4 : u4.toNat * s4.toNat < 2^28 * 2^29 := Nat.mul_lt_mul'' hub4 hsb4
    omega
  have hdb4 : d4.toNat < 2^60 := by
    have p0 : u0.toNat * r4.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub0 hr4
    have p1 : u1.toNat * r3.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub1 hr3
    have p2 : u2.toNat * r2.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub2 hr2
    have p3 : u3.toNat * r1.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub3 hr1
    have p4 : u4.toNat * r0.toNat < 2^28 * 2^26 := Nat.mul_lt_mul'' hub4 hr0
    omega
  -- carry transports (d_i.toNat as opaque atoms from here on)
  have he1' : e1.toNat = d1.toNat + d0.toNat / 67108864 := by
    subst he1
    simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow]
    omega
  have heb1 : e1.toNat < 2^61 := by omega
  have he2' : e2.toNat = d2.toNat + e1.toNat / 67108864 := by
    subst he2
    simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow]
    omega
  have heb2 : e2.toNat < 2^61 := by omega
  have he3' : e3.toNat = d3.toNat + e2.toNat / 67108864 := by
    subst he3
    simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow]
    omega
  have heb3 : e3.toNat < 2^61 := by omega
  have he4' : e4.toNat = d4.toNat + e3.toNat / 67108864 := by
    subst he4
    simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow]
    omega
  have heb4 : e4.toNat < 2^61 := by omega
  have hg0' : g0.toNat = d0.toNat % 67108864 + e4.toNat / 67108864 * 5 := by
    subst hg0
    simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod,
      UInt64.toNat_mul, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    omega
  -- output limb transports
  have ho0 : (g0 % 67108864).toNat = g0.toNat % 67108864 := by
    simp only [UInt64.toNat_mod, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  have ho1 : (e1 % 67108864 + g0 / 67108864).toNat
      = e1.toNat % 67108864 + g0.toNat / 67108864 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_div,
      UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    omega
  have ho2 : (e2 % 67108864).toNat = e2.toNat % 67108864 := by
    simp only [UInt64.toNat_mod, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  have ho3 : (e3 % 67108864).toNat = e3.toNat % 67108864 := by
    simp only [UInt64.toNat_mod, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  have ho4 : (e4 % 67108864).toNat = e4.toNat % 67108864 := by
    simp only [UInt64.toNat_mod, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  refine ⟨?_, by omega, by omega, by omega, by omega, by omega⟩
  -- value identity: express the d-sums in r-limbs so the product terms match
  -- `mul_wrap`'s shapes (rewriting cannot reach inside non-linear atoms later)
  simp only [hs1, hs2, hs3, hs4] at hd0' hd1' hd2' hd3' hd4'
  -- align the goal's product with the u-limb product
  have husum : u0.toNat + u1.toNat*2^26 + u2.toNat*2^52 + u3.toNat*2^78 + u4.toNat*2^104
      = limbsToNat h0 h1 h2 h3 h4 + (lo.toNat + hi.toNat * 2^64 + 2^128) := by
    simp only [limbsToNat]
    omega
  -- the product as the d-sum plus an explicit multiple of P
  have hmulX : (limbsToNat h0 h1 h2 h3 h4 + (lo.toNat + hi.toNat * 2^64 + 2^128))
        * (r0.toNat + r1.toNat*2^26 + r2.toNat*2^52 + r3.toNat*2^78 + r4.toNat*2^104)
      = d0.toNat + d1.toNat*2^26 + d2.toNat*2^52 + d3.toNat*2^78 + d4.toNat*2^104
      + (u1.toNat*r4.toNat + u2.toNat*r3.toNat + u3.toNat*r2.toNat + u4.toNat*r1.toNat
          + (u2.toNat*r4.toNat + u3.toNat*r3.toNat + u4.toNat*r2.toNat) * 2^26
          + (u3.toNat*r4.toNat + u4.toNat*r3.toNat) * 2^52
          + u4.toNat*r4.toNat * 2^78) * 1361129467683753853853498429727072845819 := by
    rw [← husum, hd0', hd1', hd2', hd3', hd4']
    exact mul_wrap u0.toNat u1.toNat u2.toNat u3.toNat u4.toNat
      r0.toNat r1.toNat r2.toNat r3.toNat r4.toNat
  -- finish: strip both explicit multiples of P, leaving the carry identity
  rw [P_eq, hmulX, Nat.add_mul_mod_self_right]
  simp only [limbsToNat, ho0, ho1, ho2, ho3, ho4, he1', he2', he3', he4', hg0']
  rw [← carry_fixup d0.toNat d1.toNat d2.toNat d3.toNat d4.toNat,
    Nat.add_mul_mod_self_right]
