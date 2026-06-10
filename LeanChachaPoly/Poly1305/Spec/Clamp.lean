import LeanChachaPoly.Poly1305.Spec
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NormNum.Ineq

/-!
# Poly1305 Clamp matches RFC 8439 §2.5.1

The spec defines clamping as a single `Nat` mask
(`r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff`). The RFC instead describes it
byte-wise: clear the top 4 bits of bytes 3, 7, 11, 15 and the low 2 bits of
bytes 4, 8, 12. `clamp_rfc` proves the mask realizes exactly that — those 22
bits are cleared **and every other bit is preserved** — so the compact
definition is faithful to the standard in both directions.

The second half of the file counts the *clamped key space*: clamping keeps
exactly `128 − 22 = 106` of the 128 bits free, so its image has size `2¹⁰⁶`
(`clampImage_card`) — the denominator of the clamped Poly1305 forgery
probability `8⌈L/16⌉ / 2¹⁰⁶` in `Poly1305.Security` — and every clamped value
has exactly `2²²` preimages (`clamp_fiber_card`), so a uniform 16-byte `r`
pushed through `clamp` is uniform on that key space — the distribution assumed
by the forgery probability is the one key generation produces.
-/

namespace Poly1305.Spec

/-- **Supporting.** Clamping ANDs `r` with the fixed mask, bit by bit. -/
theorem clamp_testBit (r j : Nat) :
    (clamp r).testBit j
      = (r.testBit j && (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit j) := by
  unfold clamp
  exact Nat.testBit_and r _ j

/-- The 22 bit positions cleared by clamping (RFC 8439 §2.5.1): the top 4 bits of
    bytes 3, 7, 11, 15 (positions 28–31, 60–63, 92–95, 124–127) and the low 2
    bits of bytes 4, 8, 12 (positions 32–33, 64–65, 96–97). -/
def clampClearedBits : Finset Nat :=
  {28, 29, 30, 31, 60, 61, 62, 63, 92, 93, 94, 95, 124, 125, 126, 127,
   32, 33, 64, 65, 96, 97}

set_option maxRecDepth 4000 in
/-- The mask is set exactly off the 22 cleared positions (decided by the kernel). -/
private theorem mask_bit_char : ∀ j : Fin 128,
    (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit j.val
      = !decide (j.val ∈ clampClearedBits) := by decide

/-- **Key lemma (RFC 8439 §2.5.1).** Complete bit-level characterization of clamping:
    the 22 RFC-named bits vanish in `clamp r`, and **every other bit of `r` is
    preserved** — the mask realizes exactly the RFC's byte-wise description.
    (Bits ≥ 128 are also clear: `clamp_lt`.) -/
theorem clamp_rfc (r j : Nat) (hj : j < 128) :
    (clamp r).testBit j =
      if j ∈ clampClearedBits then false else r.testBit j := by
  rw [clamp_testBit, mask_bit_char ⟨j, hj⟩]
  by_cases hmem : j ∈ clampClearedBits
  · simp [hmem]
  · simp [hmem]

/-! ## Counting the clamped key space

    Clamping is `r ↦ r &&& mask`. Two cardinality facts close the probability
    model in `Poly1305.Security`:

    - `clampImage_card`: the image has exactly `2¹⁰⁶` elements — the mask's `106`
      set bits are free, the other `22` are forced to `0` (the ε denominator);
    - `clamp_fiber_card`: every clamped value has exactly `2²²` preimages among
      the 128-bit inputs — so pushing a *uniform* 16-byte `r` through `clamp`
      gives the *uniform* distribution on the clamped key space (equal fibers),
      and drawing uniformly from `clampedKeys` coincides with the key-generation
      procedure.

    Both reduce to one generic count, `bitConstrained_card`: the numbers below
    `2ᴺ` whose bits are prescribed on a position set `Q` number `2^(N − #Q)`,
    by bijecting with Boolean assignments to the free positions. -/

open Finset

/-- A reconstructed `Nat` from a bit-assignment `f` on `Fin n` stays `< 2ⁿ`. -/
private theorem boundSum (n : Nat) (f : Fin n → Bool) :
    (∑ k : Fin n, (if f k then 2 ^ (k : Nat) else 0)) < 2 ^ n := by
  calc (∑ k : Fin n, (if f k then 2 ^ (k : Nat) else 0))
      ≤ ∑ k : Fin n, 2 ^ (k : Nat) := by
        apply Finset.sum_le_sum; intro k _; split <;> simp
    _ = ∑ k ∈ range n, 2 ^ k := by rw [Fin.sum_univ_eq_sum_range (fun k => 2 ^ k) n]
    _ = 2 ^ n - 1 := by rw [Nat.geomSum_eq (le_refl 2) n]; simp
    _ < 2 ^ n := by have : 0 < 2 ^ n := Nat.two_pow_pos n; omega

/-- The reconstructed `Nat` reads back the bit-assignment: its `m`-th bit is `f m`. -/
private theorem testBitSum (n : Nat) : ∀ (f : Fin n → Bool) (m : Nat) (hm : m < n),
    (∑ k : Fin n, (if f k then 2 ^ (k : Nat) else 0)).testBit m = f ⟨m, hm⟩ := by
  induction n with
  | zero => intro f m hm; omega
  | succ n ih =>
    intro f m hm
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    set low := ∑ i : Fin n, (if f (Fin.castSucc i) then 2 ^ (i : Nat) else 0) with hlow
    have hlowlt : low < 2 ^ n := boundSum n (fun i => f (Fin.castSucc i))
    by_cases hfn : f (Fin.last n)
    · rw [if_pos hfn]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with hmn | hmn
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hmn]
        rw [ih (fun i => f (Fin.castSucc i)) m hmn]; congr 1
      · subst hmn
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlowlt]
        simp only [Bool.not_false]
        rw [show (⟨m, hm⟩ : Fin (m + 1)) = Fin.last m from rfl]; exact hfn.symm
    · rw [if_neg hfn, Nat.add_zero]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with hmn | hmn
      · rw [ih (fun i => f (Fin.castSucc i)) m hmn]; congr 1
      · subst hmn
        rw [Nat.testBit_lt_two_pow hlowlt]
        have hfalse : f (Fin.last m) = false := by simpa using hfn
        rw [show (⟨m, hm⟩ : Fin (m + 1)) = Fin.last m from rfl, hfalse]

/-- Bit-assignments prescribed (by `v`) on a predicate's true-set are determined by
    their values off it, so there are `2^(#off)` of them. -/
private def prescribedEquiv (N : Nat) (Q : Fin N → Prop) [DecidablePred Q] (v : Fin N → Bool) :
    {f : Fin N → Bool // ∀ i, Q i → f i = v i} ≃ ({i : Fin N // ¬ Q i} → Bool) where
  toFun f i := f.val i.val
  invFun g := ⟨fun i => if h : Q i then v i else g ⟨i, h⟩, by intro i hi; simp only [hi, dif_pos]⟩
  left_inv f := by
    ext i; by_cases h : Q i
    · simp only [h, f.property i h, dif_pos]
    · simp only [h, dif_neg, not_false_iff]
  right_inv g := by funext i; simp only [i.property, dif_neg, not_false_iff]

private theorem funspace_card (N : Nat) (Q : Fin N → Prop) [DecidablePred Q] (v : Fin N → Bool) :
    (univ.filter (fun f : Fin N → Bool => ∀ i, Q i → f i = v i)).card
      = 2 ^ (univ.filter (fun i => ¬ Q i)).card := by
  rw [← Fintype.card_subtype, Fintype.card_congr (prescribedEquiv N Q v), Fintype.card_fun,
      Fintype.card_subtype]; simp

/-- **Key lemma (generic bit-prescription count).** The numbers below `2ᴺ` whose bits
    at the positions satisfying `Q` are prescribed by `v` number exactly `2^(#¬Q)`.
    Bijects each such number with its bit-assignment `k ↦ x.testBit k`;
    reconstruction is `f ↦ ∑ 2ᵏ`. -/
private theorem bitConstrained_card (N : Nat) (Q : Fin N → Prop) [DecidablePred Q]
    (v : Fin N → Bool) :
    ((range (2 ^ N)).filter (fun x => ∀ i : Fin N, Q i → x.testBit i.val = v i)).card
      = 2 ^ (univ.filter (fun i : Fin N => ¬ Q i)).card := by
  rw [← funspace_card N Q v]
  apply Finset.card_nbij'
    (i := fun x => (fun k : Fin N => x.testBit k.val))
    (j := fun f => ∑ k : Fin N, (if f k then 2 ^ (k : Nat) else 0))
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx.2
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨boundSum N f, ?_⟩
    intro i hi
    rw [testBitSum N f i.val i.isLt]
    exact hf i hi
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hx
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hp : p < N
    · rw [testBitSum N (fun k : Fin N => x.testBit k.val) p hp]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (boundSum N _)
            (Nat.pow_le_pow_right (by norm_num) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hx.1
            (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · intro f hf
    funext k
    exact testBitSum N f k.val k.isLt

/-- The clamp mask has exactly `106` set bits (`128 − 22`). Decided by the kernel
    (axiom-clean — not `native_decide`). -/
private theorem maskCount :
    (univ.filter (fun i : Fin 128 =>
      (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i.val = true)).card = 106 := by
  decide

/-- ... and `22` clear bits below position 128. -/
private theorem maskCountC :
    (univ.filter (fun i : Fin 128 =>
      (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i.val = false)).card = 22 := by
  decide

/-- **Key lemma.** The clamped key space has exactly `2¹⁰⁶` elements: a clamped
    value is exactly a 128-bit value that is `0` on the mask's clear bits, and
    the mask leaves `106` of the `128` bits free. This is the denominator of the
    clamped forgery probability in `Poly1305.Security`. -/
theorem clampImage_card :
    ((Finset.range (2 ^ 128)).image clamp).card = 2 ^ 106 := by
  have himg : (Finset.range (2 ^ 128)).image clamp
      = (Finset.range (2 ^ 128)).filter (fun y => ∀ i : Fin 128,
          (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i.val = false
            → y.testBit i.val = false) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨clamp_lt x, ?_⟩
      intro i hi
      rw [clamp_testBit, hi, Bool.and_false]
    · rintro ⟨hy, hbits⟩
      refine ⟨y, hy, ?_⟩
      apply Nat.eq_of_testBit_eq
      intro p
      rw [clamp_testBit]
      by_cases hp : p < 128
      · by_cases hM : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit p
        · rw [hM, Bool.and_true]
        · have hMf : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit p = false := by
            simpa using hM
          rw [hMf, Bool.and_false, hbits ⟨p, hp⟩ hMf]
      · have hyp : y.testBit p = false := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega)))
        rw [hyp, Bool.false_and]
  rw [himg, bitConstrained_card]
  have hfilt : (univ.filter (fun i : Fin 128 =>
      ¬ (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i.val = false))
      = univ.filter (fun i : Fin 128 =>
          (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i.val = true) := by
    apply Finset.filter_congr; intro i _
    cases h : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i.val <;> simp
  rw [hfilt, maskCount]

/-- **Key lemma (uniformity of clamping).** Every clamped value has exactly `2²²`
    preimages among the 128-bit inputs: a preimage must agree with `y` on the
    mask's `106` set bits and is free on the `22` cleared ones. Equal fibers mean
    pushing a *uniform* 16-byte `r` through `clamp` yields the *uniform*
    distribution on the `2¹⁰⁶` clamped keys — the distribution assumed by
    `poly1305_tag_forgery_prob` is the one key generation produces. -/
theorem clamp_fiber_card (y : Nat) (hy : y ∈ (Finset.range (2 ^ 128)).image clamp) :
    ((Finset.range (2 ^ 128)).filter (fun x => clamp x = y)).card = 2 ^ 22 := by
  obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.mp hy
  have hfib : (Finset.range (2 ^ 128)).filter (fun x => clamp x = clamp x₀)
      = (Finset.range (2 ^ 128)).filter (fun x => ∀ i : Fin 128,
          (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i.val = true
            → x.testBit i.val = (clamp x₀).testBit i.val) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
    intro hx
    constructor
    · rintro h i hi
      rw [← h, clamp_testBit, hi, Bool.and_true]
    · intro h
      apply Nat.eq_of_testBit_eq
      intro p
      rw [clamp_testBit]
      by_cases hp : p < 128
      · by_cases hM : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit p
        · rw [hM, Bool.and_true]; exact h ⟨p, hp⟩ hM
        · have hMf : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit p = false := by
            simpa using hM
          rw [hMf, Bool.and_false, clamp_testBit, hMf, Bool.and_false]
      · have h1 : x.testBit p = false := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
        have h2 : (clamp x₀).testBit p = false := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le (clamp_lt x₀) (Nat.pow_le_pow_right (by norm_num) (by omega)))
        rw [h1, Bool.false_and, h2]
  rw [hfib, bitConstrained_card]
  have hfilt : (univ.filter (fun i : Fin 128 =>
      ¬ (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i.val = true))
      = univ.filter (fun i : Fin 128 =>
          (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i.val = false) := by
    apply Finset.filter_congr; intro i _
    cases h : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i.val <;> simp
  rw [hfilt, maskCountC]

end Poly1305.Spec
