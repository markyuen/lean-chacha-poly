import LeanChachaPoly.Poly1305.Spec
import LeanChachaPoly.Poly1305.Spec.Sum
import LeanChachaPoly.Poly1305.Spec.Blocking
import LeanChachaPoly.Poly1305.Spec.Accumulate
import LeanChachaPoly.Poly1305.Spec.Clamp
import LeanChachaPoly.Poly1305.Spec.Tag
import LeanChachaPoly.Poly1305.Injectivity
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.GCongr

/-!
# Poly1305 Security — the almost-universal / forgery bound

This file builds the information-theoretic security argument for Poly1305 on
top of the functional spec.

The argument, in order:

1. **Blocks are field elements** (`blockToNat_lt_P`, `finalBlockToNat_lt_P`):
   every block value is `< P = 2¹³⁰ − 5`, so it has a well-defined image in `ZMod P`.
2. **Polynomial bridge** (`accumulate_cast_eq_eval`): the accumulation
   `accumulate r B`, reduced mod `P`, equals the evaluation at `r : ZMod P` of a
   polynomial whose coefficients are the message blocks `B`.
3. **Forgery bound** (`poly1305_almost_universal`): two distinct messages
   collide under at most `deg` keys `r`, where `deg` is the block count — the
   roots of a nonzero difference polynomial over the field `ZMod P`.
4. **Byte level** (`poly1305_byte_forgery`): a forger targeting a fixed
   accumulator offset mod `2¹²⁸` succeeds for at most `8 · max #blocks` keys.
5. **Tag level** (`poly1305_tag_forgery`, `poly1305_tag_forgery_prob` — the
   capstones): stated about `poly1305` itself and its 16-byte tags.
   Subtracting the two tag equations (`poly1305_value`) cancels the one-time
   pad `s`, so a forger who saw the tag of `M` and forges a tag for
   `M' ≠ M` succeeds for at most `8⌈L/16⌉` of the `2¹⁰⁶` clamped keys — the
   published Poly1305 forgery probability `8⌈L/16⌉ / 2¹⁰⁶`.

`ZMod P` is a field only when `P` is prime. `2¹³⁰ − 5` is the Poly1305 prime,
but a 40-digit primality certificate is out of scope here, so the
field-dependent results are parameterized on `[Fact (Nat.Prime P)]`.
-/

namespace Poly1305.Spec

open scoped BigOperators
open Polynomial

/-! ## Blocks are field elements (`< P`) -/

/-- The geometric bound `∑_{i<L} 255·2^(8i) = 2^(8L) − 1 < 2^(8L)`. -/
private theorem geom_lt (L : Nat) :
    (∑ i ∈ Finset.range L, 255 * 2 ^ (i * 8)) < 2 ^ (L * 8) := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, show (n + 1) * 8 = n * 8 + 8 from by ring, pow_add,
        show (2 : Nat) ^ 8 = 256 from rfl]
    omega

/-- **Supporting.** A full block, with its `2¹²⁸` high bit, still fits in the field: `< P`. -/
theorem blockToNat_lt_P (block : Block) :
    blockToNat block < P := by
  have hlt := blockToNat_lt block
  have hP : (2 : Nat) ^ 129 < P := by unfold P; norm_num
  omega

/-- **Supporting.** The final (partial) block fits in the field: `< P`. Its value is the
    little-endian sum of `L = block.length ≤ 16` bytes plus the high bit
    `2^(8L)`; the byte sum is `< 2^(8L)`, so the total is `< 2^(8L+1) ≤ 2¹²⁹ < P`. -/
theorem finalBlockToNat_lt_P (block : FinalBlock) :
    finalBlockToNat block < P := by
  -- The little-endian byte sum is `< 2^(8·len)`.
  have hbytes :
      (List.finRange block.val.length).foldl
        (fun acc i => acc + (block.val.get i).toNat * 2 ^ (i.val * 8)) 0
        < 2 ^ (block.val.length * 8) := by
    rw [foldl_add_eq_sum, Nat.zero_add]
    -- bound each term by `255 · 2^(8i)`
    have hle :
        ((List.finRange block.val.length).map
          (fun i : Fin block.val.length => (block.val.get i).toNat * 2 ^ (i.val * 8))).sum
        ≤ ((List.finRange block.val.length).map
          (fun i : Fin block.val.length => 255 * 2 ^ (i.val * 8))).sum := by
      apply List.sum_le_sum
      intro i _
      have hb : (block.val.get i).toNat ≤ 255 := by
        have := (block.val.get i).toNat_lt; omega
      exact Nat.mul_le_mul_right _ hb
    -- the constant sum is `∑_{i<len} 255·2^(8i) < 2^(8·len)`
    have hconst :
        ((List.finRange block.val.length).map
          (fun i : Fin block.val.length => 255 * 2 ^ (i.val * 8))).sum
          = ∑ i ∈ Finset.range block.val.length, 255 * 2 ^ (i * 8) := by
      rw [← Fin.sum_univ_def]
      exact Fin.sum_univ_eq_sum_range (fun k => 255 * 2 ^ (k * 8)) block.val.length
    have hgeom := geom_lt block.val.length
    rw [hconst] at hle
    omega
  -- assemble: total `< 2^(8·len) + 2^(8·len) ≤ 2^128 + 2^128 < P`
  unfold finalBlockToNat
  have hpow : (2 : Nat) ^ (block.val.length * 8) ≤ 2 ^ 128 :=
    Nat.pow_le_pow_right (by norm_num) (by have := block.property; omega)
  have hP : (2 : Nat) ^ 128 + 2 ^ 128 < P := by unfold P; norm_num
  omega

/-! ## The polynomial bridge

    `accumulate r B`, reduced mod `P`, is the evaluation at `r : ZMod P` of the
    message polynomial `msgPoly B = Σ (c, k) ∈ B.reverse.zipIdx, cⱼ · X^(k+1)`.
    This recasts the iterative MAC as a single polynomial evaluation in the
    field, which is what the root-counting forgery bound needs. -/

/-- The message polynomial: block `cⱼ` (counted from the end, position `k`) is
    the coefficient of `X^(k+1)`. Matches `evalPoly`'s index convention. -/
noncomputable def msgPoly (B : List Nat) : (ZMod P)[X] :=
  (B.reverse.zipIdx.map (fun p => C (p.1 : ZMod P) * X ^ (p.2 + 1))).sum

/-- **Supporting.** Evaluating `msgPoly` distributes over the block list. -/
theorem msgPoly_eval (B : List Nat) (r : Nat) :
    (msgPoly B).eval (r : ZMod P)
      = (B.reverse.zipIdx.map (fun p => (p.1 : ZMod P) * (r : ZMod P) ^ (p.2 + 1))).sum := by
  unfold msgPoly
  have h := map_list_sum (Polynomial.evalRingHom (r : ZMod P))
      (B.reverse.zipIdx.map (fun p => C (p.1 : ZMod P) * X ^ (p.2 + 1)))
  simp only [Polynomial.coe_evalRingHom] at h
  rw [h, List.map_map]
  apply congrArg
  apply List.map_congr_left
  intro p _
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- **Key lemma (bridge).** The Poly1305 accumulation, viewed in `ZMod P`, is the
    evaluation of the message polynomial at the key `r`. -/
theorem accumulate_cast_eq_eval (r : Nat) (B : List Nat) :
    ((accumulate r B : Nat) : ZMod P) = (msgPoly B).eval (r : ZMod P) := by
  rw [accumulate_eq_poly, msgPoly_eval, evalPoly, ZMod.natCast_mod, Nat.cast_list_sum,
    List.map_map]
  apply congrArg
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  push_cast
  ring

/-! ## Coefficients of `msgPoly`

    To show the *difference* of two message polynomials is nonzero (the heart of
    the forgery bound), we read off coefficients. Block `cⱼ` at reverse-position
    `k` is the coefficient of `X^(k+1)`; degree `0` and degrees above the block
    count vanish. -/

/-- Sum over `List.zipIdx` (with start `s`) as a `Finset.range` sum. -/
private theorem zipIdx_aux {M : Type*} [AddCommMonoid M] (L : List Nat)
    (f : Nat → Nat → M) (s : Nat) :
    ((L.zipIdx s).map (fun p => f p.1 p.2)).sum
      = ∑ k ∈ Finset.range L.length, f (L.getD k 0) (k + s) := by
  induction L generalizing s with
  | nil => simp
  | cons a t ih =>
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, ih (s + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      rw [show k + (s + 1) = k + 1 + s from by ring]
    · rw [Nat.zero_add]

/-- **Supporting.** `msgPoly` as a `Finset.range` sum (the `zipIdx` reindexed). -/
theorem msgPoly_eq_sum (B : List Nat) :
    msgPoly B = ∑ k ∈ Finset.range B.length, C (B.reverse.getD k 0 : ZMod P) * X ^ (k + 1) := by
  unfold msgPoly
  rw [zipIdx_aux B.reverse (fun a k => C (a : ZMod P) * X ^ (k + 1)) 0, List.length_reverse]

/-- The coefficient of `msgPoly B` at degree `d`: block `B.reverse[d−1]` when
    `1 ≤ d ≤ |B|`, else `0`. -/
theorem msgPoly_coeff (B : List Nat) (d : Nat) :
    (msgPoly B).coeff d
      = if 1 ≤ d ∧ d ≤ B.length then (B.reverse.getD (d - 1) 0 : ZMod P) else 0 := by
  rw [msgPoly_eq_sum, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hd0 : d = 0
  · subst hd0
    rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (by omega)]
  · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hcongr : ∀ k ∈ Finset.range B.length,
        (if d = k + 1 then (B.reverse.getD k 0 : ZMod P) else 0)
          = (if k = d - 1 then (B.reverse.getD k 0 : ZMod P) else 0) := by
      intro k _
      by_cases hk : d = k + 1
      · rw [if_pos hk, if_pos (by omega)]
      · rw [if_neg hk, if_neg (by omega)]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    rw [if_congr (show (d - 1 < B.length) ↔ (1 ≤ d ∧ d ≤ B.length) by omega) rfl rfl]

/-- Coefficient at a degree `> |B|` is zero. -/
theorem msgPoly_coeff_high (B : List Nat) (d : Nat) (hd : B.length < d) :
    (msgPoly B).coeff d = 0 := by
  rw [msgPoly_coeff, if_neg (by omega)]

/-- Coefficient at degree `k+1` (for `k < |B|`) is the reverse-indexed block. -/
theorem msgPoly_coeff_succ (B : List Nat) (k : Nat) (hk : k < B.length) :
    (msgPoly B).coeff (k + 1)
      = ((B.reverse[k]'(by rwa [List.length_reverse]) : Nat) : ZMod P) := by
  rw [msgPoly_coeff, if_pos (by omega)]
  simp only [Nat.add_sub_cancel]
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_reverse])]

/-- **Supporting.** `msgPoly B` has degree at most the block count. -/
theorem msgPoly_natDegree_le (B : List Nat) : (msgPoly B).natDegree ≤ B.length := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  exact msgPoly_coeff_high B m hm

/-! ## The difference polynomial is nonzero

    Distinct block lists give distinct polynomials, so `msgPoly B − msgPoly B'`
    is nonzero — provided the blocks are field elements (`< P`) and nonzero
    (which `toBlocks` guarantees). This is what makes the collision set finite. -/

/-- `Nat.cast` into `ZMod P` is injective on `[0, P)`. -/
private theorem cast_inj_of_lt {x y : Nat} (hx : x < P) (hy : y < P)
    (h : (x : ZMod P) = (y : ZMod P)) : x = y := by
  have hmod := (ZMod.natCast_eq_natCast_iff x y P).mp h
  unfold Nat.ModEq at hmod
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod

/-- A nonzero block (`0 < x < P`) has nonzero image in `ZMod P`. -/
private theorem cast_ne_zero_of_pos_lt {x : Nat} (hpos : 0 < x) (hlt : x < P) :
    (x : ZMod P) ≠ 0 := by
  intro h
  have hx0 : x = 0 := cast_inj_of_lt hlt P_pos (by simpa using h)
  omega

/-- An in-range reverse-indexed block is a member of the original list. -/
private theorem getD_reverse_mem (B : List Nat) (k : Nat) (hk : k < B.length) :
    B.reverse.getD k 0 ∈ B := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_reverse])]
  exact List.mem_reverse.mp (List.getElem_mem _)

/-- When `B` is strictly longer, the two polynomials differ at degree `|B|`:
    `msgPoly B` has the nonzero leading block there, `msgPoly B'` has `0`. -/
private theorem coeff_top_ne (B B' : List Nat) (hpos : ∀ b ∈ B, 0 < b ∧ b < P)
    (hlt : B'.length < B.length) :
    (msgPoly B).coeff B.length ≠ (msgPoly B').coeff B.length := by
  rw [msgPoly_coeff B B.length, if_pos (by omega), msgPoly_coeff_high B' B.length hlt]
  have hmem : B.reverse.getD (B.length - 1) 0 ∈ B := getD_reverse_mem B (B.length - 1) (by omega)
  exact cast_ne_zero_of_pos_lt (hpos _ hmem).1 (hpos _ hmem).2

/-- **Key lemma.** Distinct messages ⇒ distinct polynomials. With field-element,
    nonzero blocks, `B ≠ B'` forces `msgPoly B ≠ msgPoly B'`: either a length mismatch
    exposes a nonzero leading coefficient, or (same length) some block differs
    and the cast is injective. -/
theorem msgPoly_ne (B B' : List Nat)
    (hpos : ∀ b ∈ B, 0 < b ∧ b < P) (hpos' : ∀ b ∈ B', 0 < b ∧ b < P)
    (hne : B ≠ B') : msgPoly B ≠ msgPoly B' := by
  intro heq
  rcases lt_trichotomy B.length B'.length with hlt | heqlen | hgt
  · exact coeff_top_ne B' B hpos' hlt (congrArg (·.coeff B'.length) heq).symm
  · apply hne
    apply List.reverse_injective
    apply List.ext_getElem (by rw [List.length_reverse, List.length_reverse, heqlen])
    intro k hk hk'
    have hkB : k < B.length := by rwa [List.length_reverse] at hk
    have hkB' : k < B'.length := by rwa [List.length_reverse] at hk'
    have hco : (msgPoly B).coeff (k + 1) = (msgPoly B').coeff (k + 1) := by rw [heq]
    rw [msgPoly_coeff_succ B k hkB, msgPoly_coeff_succ B' k hkB'] at hco
    have hmemB : B.reverse[k]'(by rwa [List.length_reverse]) ∈ B :=
      List.mem_reverse.mp (List.getElem_mem _)
    have hmemB' : B'.reverse[k]'(by rwa [List.length_reverse]) ∈ B' :=
      List.mem_reverse.mp (List.getElem_mem _)
    exact cast_inj_of_lt (hpos _ hmemB).2 (hpos' _ hmemB').2 hco
  · exact coeff_top_ne B B' hpos hgt (congrArg (·.coeff B.length) heq)

/-! ## The forgery bound (almost-universal hashing)

    `ZMod P` is a field exactly when `P` is prime; `P = 2¹³⁰ − 5` is the Poly1305
    prime. Its 40-digit primality is taken as the hypothesis `[Fact P.Prime]`
    rather than discharged here (that needs a Pratt certificate). -/

/-- **Capstone.** Almost-universal hashing: over the prime field `ZMod P`, two
    distinct messages (as field-element, nonzero block lists) collide under Poly1305
    for at most `max |B| |B'|` choices of the key component `r`. The
    information-theoretic core of Poly1305 unforgeability — a colliding `r` is a root
    of the nonzero difference polynomial, and a degree-`n` polynomial over a field has
    at most `n` roots. -/
theorem poly1305_almost_universal [Fact (Nat.Prime P)] (B B' : List Nat)
    (hpos : ∀ b ∈ B, 0 < b ∧ b < P) (hpos' : ∀ b ∈ B', 0 < b ∧ b < P)
    (hne : B ≠ B') :
    (Finset.univ.filter
      (fun r : ZMod P => (msgPoly B).eval r = (msgPoly B').eval r)).card
      ≤ max B.length B'.length := by
  classical
  haveI : NeZero P := ⟨P_pos.ne'⟩
  set D : (ZMod P)[X] := msgPoly B - msgPoly B' with hD
  have hDne : D ≠ 0 := sub_ne_zero.mpr (msgPoly_ne B B' hpos hpos' hne)
  -- every colliding key is a root of the difference polynomial
  have hsub : (Finset.univ.filter
      (fun r : ZMod P => (msgPoly B).eval r = (msgPoly B').eval r))
      ⊆ D.roots.toFinset := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hDne]
    show D.eval r = 0
    rw [hD, Polynomial.eval_sub, hr.2, sub_self]
  -- ... and a nonzero polynomial has at most `natDegree` roots
  calc (Finset.univ.filter
        (fun r : ZMod P => (msgPoly B).eval r = (msgPoly B').eval r)).card
      ≤ D.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card D.roots := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := Polynomial.card_roots' D
    _ ≤ max (msgPoly B).natDegree (msgPoly B').natDegree := Polynomial.natDegree_sub_le _ _
    _ ≤ max B.length B'.length := max_le_max (msgPoly_natDegree_le B) (msgPoly_natDegree_le B')

/-! ## Almost-Δ-universal (additive offset) -/

/-- **Key lemma.** The byte-level forgery bound rests on a *Δ-universal* property:
    the forger must make `acc(M') − acc(M)` hit a specific value `c`, not just collide.
    Over the field this is the same root count applied to `D = msgPoly B − msgPoly B'
    − C c`; `D` stays nonzero for *any* constant `c` because the polynomial difference
    has no constant term (every `msgPoly` monomial is `X^(k+1)`), so degree ≥ 1 and
    subtracting a constant cannot zero it. -/
theorem poly1305_almost_delta_universal [Fact (Nat.Prime P)] (B B' : List Nat)
    (hpos : ∀ b ∈ B, 0 < b ∧ b < P) (hpos' : ∀ b ∈ B', 0 < b ∧ b < P)
    (hne : B ≠ B') (c : ZMod P) :
    (Finset.univ.filter (fun r : ZMod P =>
      (msgPoly B).eval r = (msgPoly B').eval r + c)).card
      ≤ max B.length B'.length := by
  classical
  haveI : NeZero P := ⟨P_pos.ne'⟩
  set E := msgPoly B - msgPoly B' with hE
  have hEne : E ≠ 0 := sub_ne_zero.mpr (msgPoly_ne B B' hpos hpos' hne)
  have hE0 : E.coeff 0 = 0 := by rw [hE, Polynomial.coeff_sub]; simp [msgPoly_coeff]
  set D := E - Polynomial.C c with hD
  have hDne : D ≠ 0 := by
    have hex : ∃ d, E.coeff d ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hEne (Polynomial.ext (fun n => by rw [hc n, Polynomial.coeff_zero]))
    obtain ⟨d, hd⟩ := hex
    have hd0 : d ≠ 0 := by rintro rfl; exact hd hE0
    intro hzero
    apply hd
    have : D.coeff d = 0 := by rw [hzero, Polynomial.coeff_zero]
    rwa [hD, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg hd0, sub_zero] at this
  have hsub : (Finset.univ.filter (fun r : ZMod P =>
      (msgPoly B).eval r = (msgPoly B').eval r + c)) ⊆ D.roots.toFinset := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hDne]
    show D.eval r = 0
    rw [hD, hE, Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_C, hr.2]
    ring
  calc (Finset.univ.filter (fun r : ZMod P =>
        (msgPoly B).eval r = (msgPoly B').eval r + c)).card
      ≤ D.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card D.roots := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := Polynomial.card_roots' D
    _ ≤ max E.natDegree (Polynomial.C c).natDegree := by rw [hD]; exact Polynomial.natDegree_sub_le _ _
    _ = E.natDegree := by rw [Polynomial.natDegree_C]; exact max_eq_left (Nat.zero_le _)
    _ ≤ max (msgPoly B).natDegree (msgPoly B').natDegree := by rw [hE]; exact Polynomial.natDegree_sub_le _ _
    _ ≤ max B.length B'.length := max_le_max (msgPoly_natDegree_le B) (msgPoly_natDegree_le B')

/-- **Supporting.** Union-bound reduction toward the byte-level forgery bound: if the
    keys causing a byte-level collision are covered by a finite set `cands` of
    field-offsets `c` (each collision realizing `eval B = eval B' + c`), then the
    number of such keys is at most `|cands| · max #blocks`. -/
theorem collision_union_bound [Fact (Nat.Prime P)] (B B' : List Nat)
    (hpos : ∀ b ∈ B, 0 < b ∧ b < P) (hpos' : ∀ b ∈ B', 0 < b ∧ b < P)
    (hne : B ≠ B') (cands : Finset (ZMod P)) :
    (Finset.univ.filter (fun r : ZMod P =>
      ∃ c ∈ cands, (msgPoly B).eval r = (msgPoly B').eval r + c)).card
      ≤ cands.card * max B.length B'.length := by
  classical
  have hsub : (Finset.univ.filter (fun r : ZMod P =>
      ∃ c ∈ cands, (msgPoly B).eval r = (msgPoly B').eval r + c))
      ⊆ cands.biUnion (fun c => Finset.univ.filter (fun r : ZMod P =>
          (msgPoly B).eval r = (msgPoly B').eval r + c)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨c, hc, heq⟩ := hr.2
    rw [Finset.mem_biUnion]
    exact ⟨c, hc, Finset.mem_filter.mpr ⟨Finset.mem_univ r, heq⟩⟩
  calc (Finset.univ.filter (fun r : ZMod P =>
        ∃ c ∈ cands, (msgPoly B).eval r = (msgPoly B').eval r + c)).card
      ≤ (cands.biUnion (fun c => Finset.univ.filter (fun r : ZMod P =>
          (msgPoly B).eval r = (msgPoly B').eval r + c))).card := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ cands, (Finset.univ.filter (fun r : ZMod P =>
          (msgPoly B).eval r = (msgPoly B').eval r + c)).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ cands, max B.length B'.length :=
          Finset.sum_le_sum (fun c _ => poly1305_almost_delta_universal B B' hpos hpos' hne c)
    _ = cands.card * max B.length B'.length := by rw [Finset.sum_const, smul_eq_mul]

/-! ## The candidate count (the `8` in `8⌈L/16⌉`)

    The accumulators lie in `[0, P)` with `P < 4·2¹²⁸`, so an integer difference
    of two of them lies in `(−P, P)`. Such a difference congruent to a fixed
    `Δ mod 2¹²⁸` is one of the 8 candidates `Δ%2¹²⁸ + k·2¹²⁸` for `k ∈ [−4, 3]`
    — this is exactly what bounds `|cands| ≤ 8`. -/

/-- **Supporting.** Every integer in `(−P, P)` congruent to `Δ mod 2¹²⁸` is one of the 8
    candidates `Δ%2¹²⁸ + k·2¹²⁸`, `k ∈ [−4, 3]`. -/
theorem candidate_cover (Δ d : ℤ) (h1 : -(P : ℤ) < d) (h2 : d < (P : ℤ))
    (h3 : d % 2 ^ 128 = Δ % 2 ^ 128) :
    d ∈ (Finset.Icc (-4 : ℤ) 3).image (fun k => Δ % 2 ^ 128 + k * 2 ^ 128) := by
  have hP : (P : ℤ) = 2 ^ 130 - 5 := by unfold P; omega
  rw [hP] at h1 h2
  rw [Finset.mem_image]
  refine ⟨(d - Δ % 2 ^ 128) / 2 ^ 128, ?_, ?_⟩
  · rw [Finset.mem_Icc]; omega
  · omega

/-- **Supporting.** The candidate set has at most 8 elements — the `8` of the `8⌈L/16⌉` bound. -/
theorem candidate_card (Δ : ℤ) :
    ((Finset.Icc (-4 : ℤ) 3).image (fun k => Δ % 2 ^ 128 + k * 2 ^ 128)).card ≤ 8 :=
  le_trans Finset.card_image_le (by decide)

/-- **Key lemma.** The canonical representative `((msgPoly B).eval r).val` of the
    field evaluation *is* the spec accumulator `accumulate r B` (both lie in `[0, P)`),
    so the byte-level bound below applies to the accumulator the spec computes. -/
theorem accumulate_eq_eval_val (r : Nat) (B : List Nat) :
    accumulate r B = ((msgPoly B).eval (r : ZMod P)).val := by
  haveI : NeZero P := ⟨P_pos.ne'⟩
  rw [← accumulate_cast_eq_eval, ZMod.val_natCast_of_lt (accumulate_lt_P r B)]

/-! ## The byte-level forgery bound -/

/-- **Key lemma.** The byte-level Poly1305 forgery bound — the `8⌈L/16⌉` factor.
    The accumulator for `B` at key `r` is the canonical representative
    `((msgPoly B).eval r).val ∈ [0, P)`. A forger targeting a fixed offset
    `Δ mod 2¹²⁸` succeeds for at most `8 · max #blocks` keys: each key realizes
    one of the ≤ 8 field-offsets `c` (`candidate_cover`), and each offset is hit
    by at most `max #blocks` keys (the Δ-universal root count). Fixing `Δ`
    models the forger's situation: `Δ` is determined by the observed tag and
    the forged tag — `poly1305_tag_forgery` below carries this out at the tag
    level, deriving the cancellation of the one-time pad `s`. -/
theorem poly1305_byte_forgery [Fact (Nat.Prime P)] (B B' : List Nat)
    (hpos : ∀ b ∈ B, 0 < b ∧ b < P) (hpos' : ∀ b ∈ B', 0 < b ∧ b < P)
    (hne : B ≠ B') (Δ : ℤ) :
    (Finset.univ.filter (fun r : ZMod P =>
      (((msgPoly B).eval r).val : ℤ) - ((msgPoly B').eval r).val ≡ Δ [ZMOD 2 ^ 128])).card
      ≤ 8 * max B.length B'.length := by
  classical
  haveI : NeZero P := ⟨P_pos.ne'⟩
  set cands : Finset (ZMod P) :=
    ((Finset.Icc (-4 : ℤ) 3).image (fun k => Δ % 2 ^ 128 + k * 2 ^ 128)).image
      (fun d : ℤ => (d : ZMod P)) with hcands
  have hcard : cands.card ≤ 8 := le_trans Finset.card_image_le (candidate_card Δ)
  have hcov : (Finset.univ.filter (fun r : ZMod P =>
      (((msgPoly B).eval r).val : ℤ) - ((msgPoly B').eval r).val ≡ Δ [ZMOD 2 ^ 128]))
      ⊆ Finset.univ.filter (fun r : ZMod P =>
          ∃ c ∈ cands, (msgPoly B).eval r = (msgPoly B').eval r + c) := by
    intro r hr
    rw [Finset.mem_filter] at hr ⊢
    refine ⟨hr.1, ?_⟩
    have hav : ((msgPoly B).eval r).val < P := ZMod.val_lt _
    have hav' : ((msgPoly B').eval r).val < P := ZMod.val_lt _
    set e : ℤ := (((msgPoly B).eval r).val : ℤ) - ((msgPoly B').eval r).val with he
    have hmem := candidate_cover Δ e (by simp only [he]; omega) (by simp only [he]; omega) hr.2
    refine ⟨(e : ZMod P), ?_, ?_⟩
    · rw [hcands, Finset.mem_image]; exact ⟨e, hmem, rfl⟩
    · rw [he]; push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; ring
  calc (Finset.univ.filter (fun r : ZMod P =>
        (((msgPoly B).eval r).val : ℤ) - ((msgPoly B').eval r).val ≡ Δ [ZMOD 2 ^ 128])).card
      ≤ _ := Finset.card_le_card hcov
    _ ≤ cands.card * max B.length B'.length := collision_union_bound B B' hpos hpos' hne cands
    _ ≤ 8 * max B.length B'.length := Nat.mul_le_mul_right _ hcard

/-! ## Lifting the bound to messages

    `toBlocks` outputs exactly the field-element, nonzero blocks the bound needs,
    so the hypotheses of `poly1305_almost_universal` are automatic for any
    message. -/

/-- Every block produced by `toBlocks` is a nonzero field element: full blocks
    carry the `2¹²⁸` high bit, the final block the `2^(8·len)` bit. -/
private theorem goPos (bs : List UInt8) : ∀ b ∈ toBlockNats.go bs, 0 < b ∧ b < P := by
  induction bs using toBlockNats.go.induct with
  | case1 => intro b hb; simp [toBlockNats.go] at hb
  | case2 bs hne _block _rest hlen ih =>
    rw [go_cons bs hne, dif_pos hlen]
    intro b hb
    rcases List.mem_cons.mp hb with h | h
    · subst h
      have hge := blockToNat_ge ⟨bs.take 16, hlen⟩
      exact ⟨by omega, blockToNat_lt_P ⟨bs.take 16, hlen⟩⟩
    · exact ih b h
  | case3 bs hne _block hlen =>
    rw [go_cons bs hne, dif_neg hlen]
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    refine ⟨?_, finalBlockToNat_lt_P ⟨bs.take 16, List.length_take_le 16 bs⟩⟩
    unfold finalBlockToNat
    have : 0 < 2 ^ ((⟨bs.take 16, List.length_take_le 16 bs⟩ : FinalBlock).val.length * 8) := by
      positivity
    omega

/-- **Supporting.** Every `toBlockNats` block is a nonzero field element (`0 < b < P`). -/
theorem toBlockNats_pos (msg : List UInt8) : ∀ b ∈ toBlockNats msg, 0 < b ∧ b < P := by
  unfold toBlockNats; exact goPos msg

/-- **Capstone.** Message-level almost-universality: for any two distinct messages
    `M ≠ M'`, the Poly1305 polynomials collide for at most `max #blocks` keys
    `r : ZMod P`. The encoding injectivity (`toBlockNats_inj`, from `Injectivity`)
    lifts the block-list hypothesis to plain message inequality. -/
theorem poly1305_almost_universal_msg' [Fact (Nat.Prime P)] (M M' : List UInt8)
    (hne : M ≠ M') :
    (Finset.univ.filter (fun r : ZMod P =>
      (msgPoly (blockNats (toBlocks M))).eval r
        = (msgPoly (blockNats (toBlocks M'))).eval r)).card
      ≤ max (blockNats (toBlocks M)).length (blockNats (toBlocks M')).length := by
  rw [blockNats_toBlocks, blockNats_toBlocks]
  exact poly1305_almost_universal (toBlockNats M) (toBlockNats M')
    (toBlockNats_pos M) (toBlockNats_pos M')
    (fun h => hne (toBlockNats_inj M M' h))

/-! ## The clamped forgery probability `8⌈L/16⌉ / 2¹⁰⁶`

    The byte-level bound above counts keys `r` over the *whole* field `ZMod P`.
    In the construction, `r` is drawn uniformly from the `2¹⁰⁶` clamped 128-bit values
    (`Poly1305.Spec.clampImage_card`). Restricting the count to that subset and
    dividing by its size turns the combinatorial bound into the published
    information-theoretic forgery probability. -/

/-- The clamped Poly1305 key component `r`, as it ranges (in the field) over all
    clamped 128-bit values. `clampedKeys_card` shows this set has size `2¹⁰⁶`, and
    `clamp_fiber_card` shows every element has exactly `2²²` clamp-preimages — so
    the uniform distribution on this set is what a uniform 16-byte `r` pushed
    through `clamp` actually produces. -/
noncomputable def clampedKeys : Finset (ZMod P) :=
  (Finset.range (2 ^ 128)).image (fun x => ((clamp x : Nat) : ZMod P))

/-- **Key lemma.** The clamped key set has exactly `2¹⁰⁶` field elements: the
    `2¹⁰⁶` clamped `Nat` values (`clampImage_card`) stay distinct in `ZMod P`
    because each is `< 2¹²⁸ < P`, so the cast is injective on them. -/
theorem clampedKeys_card : clampedKeys.card = 2 ^ 106 := by
  have hPlt : (2 : Nat) ^ 128 < P := by unfold P; norm_num
  unfold clampedKeys
  rw [show (fun x => ((clamp x : Nat) : ZMod P)) = (fun n : Nat => (n : ZMod P)) ∘ clamp from rfl,
      ← Finset.image_image, Finset.card_image_of_injOn, clampImage_card]
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range] at ha hb
  obtain ⟨xa, _, rfl⟩ := ha
  obtain ⟨xb, _, rfl⟩ := hb
  exact cast_inj_of_lt (lt_trans (clamp_lt xa) hPlt) (lt_trans (clamp_lt xb) hPlt) hab

/-- **Key lemma.** The clamped forgery probability at the accumulator level. Drawing
    the key `r` uniformly from the `2¹⁰⁶` clamped values, the fraction that let a
    forger hit a fixed offset `Δ mod 2¹²⁸` is at most `8·max #blocks / 2¹⁰⁶`. The
    numerator carries from the full-field count (`poly1305_byte_forgery`): the bad
    clamped keys are a subset of the bad field keys, so clamping never *adds*
    forgeries; the denominator is `clampedKeys_card`. The tag-level capstone
    (`poly1305_tag_forgery_prob`) restates this at the level of `poly1305` outputs. -/
theorem poly1305_clamped_forgery_prob [Fact (Nat.Prime P)] (B B' : List Nat)
    (hpos : ∀ b ∈ B, 0 < b ∧ b < P) (hpos' : ∀ b ∈ B', 0 < b ∧ b < P)
    (hne : B ≠ B') (Δ : ℤ) :
    ((clampedKeys.filter (fun r : ZMod P =>
        (((msgPoly B).eval r).val : ℤ) - ((msgPoly B').eval r).val ≡ Δ [ZMOD 2 ^ 128])).card : ℝ)
      / clampedKeys.card
      ≤ (8 * max B.length B'.length : ℝ) / 2 ^ 106 := by
  have hbad : (clampedKeys.filter (fun r : ZMod P =>
      (((msgPoly B).eval r).val : ℤ) - ((msgPoly B').eval r).val ≡ Δ [ZMOD 2 ^ 128])).card
      ≤ 8 * max B.length B'.length :=
    calc (clampedKeys.filter _).card
        ≤ (Finset.univ.filter (fun r : ZMod P =>
            (((msgPoly B).eval r).val : ℤ) - ((msgPoly B').eval r).val ≡ Δ [ZMOD 2 ^ 128])).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      _ ≤ 8 * max B.length B'.length := poly1305_byte_forgery B B' hpos hpos' hne Δ
  rw [clampedKeys_card, Nat.cast_pow, Nat.cast_ofNat]
  gcongr
  exact_mod_cast hbad

/-! ## The tag-level forgery theorem

    Everything above counts keys by their *accumulator* behavior. These final
    theorems are stated about `poly1305` itself and its 16-byte tags: if a key
    produces tag `t` on `M` and tag `t'` on `M' ≠ M`, subtracting the two tag
    equations (`poly1305_value`) cancels the one-time pad `s`, and the key's `r`
    lands in the byte-level bad set at the offset `Δ = leToNat16 t − leToNat16 t'`
    determined by the two tags. Fixing `Δ` therefore models the one-shot forger:
    `Δ` is computable from the observed tag and the forged tag. -/

open scoped Classical in
/-- **Capstone.** The tag-level Poly1305 forgery bound, stated about `poly1305` itself.
    For distinct messages `M ≠ M'` and any tag pair `(t, t')`, the clamped keys `r`
    admitting *any* key (i.e. any pad `s`) that tags `M` as `t` and `M'` as `t'`
    number at most `8 · max ⌈|M|/16⌉ ⌈|M'|/16⌉` — the published `8⌈L/16⌉` factor,
    with `⌈L/16⌉` written as `(L + 15) / 16`. -/
theorem poly1305_tag_forgery [Fact (Nat.Prime P)] (M M' : List UInt8)
    (hne : M ≠ M') (t t' : Bytes 16) :
    (clampedKeys.filter (fun r : ZMod P =>
      ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
        poly1305 key M = t ∧ poly1305 key M' = t')).card
      ≤ 8 * max ((M.length + 15) / 16) ((M'.length + 15) / 16) := by
  classical
  haveI : NeZero P := ⟨P_pos.ne'⟩
  have hpos : ∀ b ∈ blockNats (toBlocks M), 0 < b ∧ b < P := by
    rw [blockNats_toBlocks]; exact toBlockNats_pos M
  have hpos' : ∀ b ∈ blockNats (toBlocks M'), 0 < b ∧ b < P := by
    rw [blockNats_toBlocks]; exact toBlockNats_pos M'
  have hBne : blockNats (toBlocks M) ≠ blockNats (toBlocks M') := by
    rw [blockNats_toBlocks, blockNats_toBlocks]
    exact fun h => hne (toBlockNats_inj M M' h)
  -- every successful key lands in the byte-level bad set at Δ = leToNat16 t − leToNat16 t'
  have hsub : (clampedKeys.filter (fun r : ZMod P =>
      ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
        poly1305 key M = t ∧ poly1305 key M' = t'))
      ⊆ Finset.univ.filter (fun r : ZMod P =>
          ((((msgPoly (blockNats (toBlocks M))).eval r).val : ℤ)
            - ((msgPoly (blockNats (toBlocks M'))).eval r).val)
            ≡ ((leToNat16 t : ℤ) - leToNat16 t') [ZMOD 2 ^ 128]) := by
    intro r hr
    rw [Finset.mem_filter] at hr ⊢
    obtain ⟨-, key, hkey, ht, ht'⟩ := hr
    refine ⟨Finset.mem_univ _, ?_⟩
    -- the accumulators are the canonical field representatives
    have hacc : accumulate (extractR key) (blockNats (toBlocks M))
        = ((msgPoly (blockNats (toBlocks M))).eval r).val := by
      rw [accumulate_eq_eval_val, hkey]
    have hacc' : accumulate (extractR key) (blockNats (toBlocks M'))
        = ((msgPoly (blockNats (toBlocks M'))).eval r).val := by
      rw [accumulate_eq_eval_val, hkey]
    -- the two tag equations, read back through the faithful serialization
    have e1 : (accumulate (extractR key) (blockNats (toBlocks M)) + extractS key) % 2 ^ 128
        = leToNat16 t := by
      rw [← poly1305_value key M, ht]
    have e2 : (accumulate (extractR key) (blockNats (toBlocks M')) + extractS key) % 2 ^ 128
        = leToNat16 t' := by
      rw [← poly1305_value key M', ht']
    show ((((msgPoly (blockNats (toBlocks M))).eval r).val : ℤ)
            - ((msgPoly (blockNats (toBlocks M'))).eval r).val) % 2 ^ 128
        = ((leToNat16 t : ℤ) - leToNat16 t') % 2 ^ 128
    rw [← hacc, ← hacc']
    -- tags are reduced mod 2¹²⁸
    have hu : leToNat16 t < 2 ^ 128 := by rw [← e1]; exact Nat.mod_lt _ (by positivity)
    have hu' : leToNat16 t' < 2 ^ 128 := by rw [← e2]; exact Nat.mod_lt _ (by positivity)
    -- recast the two tag equations in ℤ
    have h1 : ((accumulate (extractR key) (blockNats (toBlocks M)) : ℤ) + extractS key) % 2 ^ 128
        = (leToNat16 t : ℤ) := by
      have h := congrArg (fun n : ℕ => (n : ℤ)) e1
      push_cast at h
      exact h
    have h2 : ((accumulate (extractR key) (blockNats (toBlocks M')) : ℤ) + extractS key) % 2 ^ 128
        = (leToNat16 t' : ℤ) := by
      have h := congrArg (fun n : ℕ => (n : ℤ)) e2
      push_cast at h
      exact h
    -- subtract: the one-time pad `s` cancels
    have m1 : ((accumulate (extractR key) (blockNats (toBlocks M)) : ℤ) + extractS key)
        ≡ (leToNat16 t : ℤ) [ZMOD 2 ^ 128] :=
      h1.trans (Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hu)).symm
    have m2 : ((accumulate (extractR key) (blockNats (toBlocks M')) : ℤ) + extractS key)
        ≡ (leToNat16 t' : ℤ) [ZMOD 2 ^ 128] :=
      h2.trans (Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hu')).symm
    have hfin := Int.ModEq.sub m1 m2
    simpa [add_sub_add_right_eq_sub] using hfin
  calc (clampedKeys.filter (fun r : ZMod P =>
        ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
          poly1305 key M = t ∧ poly1305 key M' = t')).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ 8 * max (blockNats (toBlocks M)).length (blockNats (toBlocks M')).length :=
        poly1305_byte_forgery _ _ hpos hpos' hBne _
    _ = 8 * max ((M.length + 15) / 16) ((M'.length + 15) / 16) := by
        rw [blockNats_length, blockNats_length]

open scoped Classical in
/-- **Capstone.** The published Poly1305 forgery probability `8⌈L/16⌉ / 2¹⁰⁶`, at the
    tag level: with the key component `r` uniform over the `2¹⁰⁶` clamped values, a
    forger who must turn an observed tag `t` on `M` into a tag `t'` on `M' ≠ M`
    succeeds with probability at most `8 · max ⌈|M|/16⌉ ⌈|M'|/16⌉ / 2¹⁰⁶`. -/
theorem poly1305_tag_forgery_prob [Fact (Nat.Prime P)] (M M' : List UInt8)
    (hne : M ≠ M') (t t' : Bytes 16) :
    ((clampedKeys.filter (fun r : ZMod P =>
      ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
        poly1305 key M = t ∧ poly1305 key M' = t')).card : ℝ)
      / clampedKeys.card
      ≤ ((8 * max ((M.length + 15) / 16) ((M'.length + 15) / 16) : ℕ) : ℝ) / 2 ^ 106 := by
  rw [clampedKeys_card, Nat.cast_pow, Nat.cast_ofNat]
  gcongr
  exact_mod_cast poly1305_tag_forgery M M' hne t t'

/-! ## Adversary-as-function formulation

    `poly1305_tag_forgery` fixes the forged pair `(M', t')`. A deterministic
    forger is a function of what it observes: given the genuine tag `t` on the
    known message `M`, it outputs a candidate `(M', t') = A t`. Quantifying over
    every such function `A` turns "quantified over every possible attacker" into a
    theorem rather than a prose argument — the key count is unchanged, since `A t`
    is determined once `t` is fixed. `poly1305_adversary_forgery_multi` adds the
    `v`-attempt union bound. -/

open scoped Classical in
/-- **Capstone.** Forgery bound against an arbitrary deterministic forger `A`. For
    any function mapping an observed tag to a forged `(message, tag)` with
    `(A t).1 ≠ M`, the clamped keys consistent with the observed tag `t` on `M`
    under which `A` also forges number at most `8 · max ⌈|M|/16⌉ ⌈|(A t).1|/16⌉`.
    Reduces to `poly1305_tag_forgery` at `M' := (A t).1`, `t' := (A t).2`. -/
theorem poly1305_adversary_forgery [Fact (Nat.Prime P)]
    (M : List UInt8) (t : Bytes 16)
    (A : Bytes 16 → List UInt8 × Bytes 16) (hne : (A t).1 ≠ M) :
    (clampedKeys.filter (fun r : ZMod P =>
      ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
        poly1305 key M = t ∧ poly1305 key (A t).1 = (A t).2)).card
      ≤ 8 * max ((M.length + 15) / 16) (((A t).1.length + 15) / 16) :=
  poly1305_tag_forgery M (A t).1 (Ne.symm hne) t (A t).2

open scoped Classical in
/-- **Capstone.** The adversary forgery probability: against any deterministic
    forger `A`, the fraction of clamped keys (uniform over the `2¹⁰⁶` values)
    consistent with the observed tag under which `A` forges is at most
    `8 · max ⌈|M|/16⌉ ⌈|(A t).1|/16⌉ / 2¹⁰⁶`. -/
theorem poly1305_adversary_forgery_prob [Fact (Nat.Prime P)]
    (M : List UInt8) (t : Bytes 16)
    (A : Bytes 16 → List UInt8 × Bytes 16) (hne : (A t).1 ≠ M) :
    ((clampedKeys.filter (fun r : ZMod P =>
      ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
        poly1305 key M = t ∧ poly1305 key (A t).1 = (A t).2)).card : ℝ)
      / clampedKeys.card
      ≤ ((8 * max ((M.length + 15) / 16) (((A t).1.length + 15) / 16) : ℕ) : ℝ) / 2 ^ 106 :=
  poly1305_tag_forgery_prob M (A t).1 (Ne.symm hne) t (A t).2

open scoped Classical in
/-- **Capstone.** The `v`-attempt union bound. A forger that produces `v` candidate
    forgeries `A 0, …, A (v-1)` succeeds for at most `v` times the single-shot
    bound: if every candidate message has length `≤ L` and differs from `M`, the
    clamped keys under which *some* attempt forges number at most `v · 8⌈L/16⌉`. -/
theorem poly1305_adversary_forgery_multi [Fact (Nat.Prime P)]
    (M : List UInt8) (t : Bytes 16) (v : ℕ)
    (A : Fin v → List UInt8 × Bytes 16) (hne : ∀ i, (A i).1 ≠ M)
    (L : ℕ) (hL : M.length ≤ L) (hLi : ∀ i, (A i).1.length ≤ L) :
    (clampedKeys.filter (fun r : ZMod P =>
      ∃ i : Fin v, ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
        poly1305 key M = t ∧ poly1305 key (A i).1 = (A i).2)).card
      ≤ v * (8 * ((L + 15) / 16)) := by
  classical
  -- the ∃ i filter is the union of the per-attempt filters
  have hunion : (clampedKeys.filter (fun r : ZMod P =>
      ∃ i : Fin v, ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
        poly1305 key M = t ∧ poly1305 key (A i).1 = (A i).2))
      = (Finset.univ : Finset (Fin v)).biUnion (fun i =>
          clampedKeys.filter (fun r : ZMod P =>
            ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
              poly1305 key M = t ∧ poly1305 key (A i).1 = (A i).2)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hr, i, h⟩; exact ⟨i, hr, h⟩
    · rintro ⟨i, hr, h⟩; exact ⟨hr, i, h⟩
  rw [hunion]
  calc ((Finset.univ : Finset (Fin v)).biUnion (fun i =>
          clampedKeys.filter (fun r : ZMod P =>
            ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
              poly1305 key M = t ∧ poly1305 key (A i).1 = (A i).2))).card
      ≤ ∑ i : Fin v, (clampedKeys.filter (fun r : ZMod P =>
          ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
            poly1305 key M = t ∧ poly1305 key (A i).1 = (A i).2)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin v, 8 * ((L + 15) / 16) := by
        apply Finset.sum_le_sum
        intro i _
        have hLi' := hLi i
        have hbound := poly1305_tag_forgery M (A i).1 (Ne.symm (hne i)) t (A i).2
        have hm : max ((M.length + 15) / 16) (((A i).1.length + 15) / 16) ≤ (L + 15) / 16 :=
          max_le (Nat.div_le_div_right (by omega)) (Nat.div_le_div_right (by omega))
        exact hbound.trans (Nat.mul_le_mul (Nat.le_refl 8) hm)
    _ = v * (8 * ((L + 15) / 16)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

open scoped Classical in
/-- **Capstone.** The `v`-attempt forgery probability: against a forger making `v`
    attempts (every candidate of length `≤ L`, distinct from `M`), the fraction of
    clamped keys under which some attempt forges is at most `v · 8⌈L/16⌉ / 2¹⁰⁶`. -/
theorem poly1305_adversary_forgery_multi_prob [Fact (Nat.Prime P)]
    (M : List UInt8) (t : Bytes 16) (v : ℕ)
    (A : Fin v → List UInt8 × Bytes 16) (hne : ∀ i, (A i).1 ≠ M)
    (L : ℕ) (hL : M.length ≤ L) (hLi : ∀ i, (A i).1.length ≤ L) :
    ((clampedKeys.filter (fun r : ZMod P =>
      ∃ i : Fin v, ∃ key : Key, ((extractR key : Nat) : ZMod P) = r ∧
        poly1305 key M = t ∧ poly1305 key (A i).1 = (A i).2)).card : ℝ)
      / clampedKeys.card
      ≤ ((v * (8 * ((L + 15) / 16)) : ℕ) : ℝ) / 2 ^ 106 := by
  rw [clampedKeys_card, Nat.cast_pow, Nat.cast_ofNat]
  gcongr
  exact_mod_cast poly1305_adversary_forgery_multi M t v A hne L hL hLi

end Poly1305.Spec
