import LeanChachaPoly.Poly1305.Spec
import LeanChachaPoly.Poly1305.Spec.Blocking
import LeanChachaPoly.Poly1305.Spec.Accumulate
import Mathlib

/-!
# Poly1305 Security — the almost-universal / forgery bound

This file builds the information-theoretic security argument for Poly1305 on
top of the functional spec.

The argument, in order:

1. **Blocks are field elements** (`blockToNat_lt_P`, `finalBlockToNat_lt_P`):
   every block produced by `toBlocks` is `< P = 2¹³⁰ − 5`, so it has a
   well-defined image in `ZMod P`.
2. **Polynomial bridge** (`accumulate_cast_eq_eval`): the accumulation
   `accumulate r (toBlocks msg)`, reduced mod `P`, equals the evaluation at
   `r : ZMod P` of a polynomial whose coefficients are the message blocks.
3. **Forgery bound** (`poly1305_almost_universal`): two distinct messages
   collide under at most `deg` keys `r`, where `deg` is the block count — the
   roots of a nonzero difference polynomial over the field `ZMod P`.

`ZMod P` is a field only when `P` is prime. `2¹³⁰ − 5` is the Poly1305 prime,
but a 40-digit primality certificate is out of scope here, so the
field-dependent results are parameterized on `[Fact (Nat.Prime P)]`.
-/

namespace Poly1305.Spec

open scoped BigOperators

/-! ## Blocks are field elements (`< P`) -/

/-- Folding `(acc + g i)` over a list is the running sum (local copy; the one in
    `Blocking.lean` is `private`). -/
private theorem foldl_add_eq_sum {α : Type*} (l : List α) (g : α → Nat) (init : Nat) :
    l.foldl (fun acc i => acc + g i) init = init + (l.map g).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih => simp [ih]; ring

/-- The geometric bound `∑_{i<L} 255·2^(8i) = 2^(8L) − 1 < 2^(8L)`. -/
private theorem geom_lt (L : Nat) :
    (∑ i ∈ Finset.range L, 255 * 2 ^ (i * 8)) < 2 ^ (L * 8) := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, show (n + 1) * 8 = n * 8 + 8 from by ring, pow_add,
        show (2 : Nat) ^ 8 = 256 from rfl]
    omega

/-- A full block, with its `2¹²⁸` high bit, still fits in the field: `< P`. -/
theorem blockToNat_lt_P (block : List UInt8) (h : block.length = 16) :
    blockToNat block h < P := by
  have hlt := blockToNat_lt block h
  have hP : (2 : Nat) ^ 129 < P := by unfold P; norm_num
  omega

/-- The final (partial) block fits in the field: `< P`. Its value is the
    little-endian sum of `L = block.length ≤ 16` bytes plus the high bit
    `2^(8L)`; the byte sum is `< 2^(8L)`, so the total is `< 2^(8L+1) ≤ 2¹²⁹ < P`. -/
theorem finalBlockToNat_lt_P (block : List UInt8) (h : block.length ≤ 16) :
    finalBlockToNat block h < P := by
  -- The little-endian byte sum is `< 2^(8·len)`.
  have hbytes :
      (List.finRange block.length).foldl
        (fun acc i => acc + (block.get i).toNat * 2 ^ (i.val * 8)) 0
        < 2 ^ (block.length * 8) := by
    rw [foldl_add_eq_sum, Nat.zero_add]
    -- bound each term by `255 · 2^(8i)`
    have hle :
        ((List.finRange block.length).map
          (fun i : Fin block.length => (block.get i).toNat * 2 ^ (i.val * 8))).sum
        ≤ ((List.finRange block.length).map
          (fun i : Fin block.length => 255 * 2 ^ (i.val * 8))).sum := by
      apply List.sum_le_sum
      intro i _
      have hb : (block.get i).toNat ≤ 255 := by
        have := (block.get i).toNat_lt; omega
      exact Nat.mul_le_mul_right _ hb
    -- the constant sum is `∑_{i<len} 255·2^(8i) < 2^(8·len)`
    have hconst :
        ((List.finRange block.length).map
          (fun i : Fin block.length => 255 * 2 ^ (i.val * 8))).sum
          = ∑ i ∈ Finset.range block.length, 255 * 2 ^ (i * 8) := by
      rw [← Fin.sum_univ_def]
      exact Fin.sum_univ_eq_sum_range (fun k => 255 * 2 ^ (k * 8)) block.length
    have hgeom := geom_lt block.length
    rw [hconst] at hle
    omega
  -- assemble: total `< 2^(8·len) + 2^(8·len) ≤ 2^128 + 2^128 < P`
  unfold finalBlockToNat
  have hpow : (2 : Nat) ^ (block.length * 8) ≤ 2 ^ 128 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hP : (2 : Nat) ^ 128 + 2 ^ 128 < P := by unfold P; norm_num
  omega

/-! ## The polynomial bridge

    `accumulate r B`, reduced mod `P`, is the evaluation at `r : ZMod P` of the
    message polynomial `msgPoly B = Σ (c, k) ∈ B.reverse.zipIdx, cⱼ · X^(k+1)`.
    This recasts the iterative MAC as a single polynomial evaluation in the
    field, which is what the root-counting forgery bound needs. -/

open Polynomial in
/-- The message polynomial: block `cⱼ` (counted from the end, position `k`) is
    the coefficient of `X^(k+1)`. Matches `evalPoly`'s index convention. -/
noncomputable def msgPoly (B : List Nat) : (ZMod P)[X] :=
  (B.reverse.zipIdx.map (fun p => C (p.1 : ZMod P) * X ^ (p.2 + 1))).sum

open Polynomial in
/-- Evaluating `msgPoly` distributes over the block list. -/
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

/-- **Bridge**: the Poly1305 accumulation, viewed in `ZMod P`, is the evaluation
    of the message polynomial at the key `r`. -/
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

open Polynomial in
/-- `msgPoly` as a `Finset.range` sum (the `zipIdx` reindexed). -/
theorem msgPoly_eq_sum (B : List Nat) :
    msgPoly B = ∑ k ∈ Finset.range B.length, C (B.reverse.getD k 0 : ZMod P) * X ^ (k + 1) := by
  unfold msgPoly
  rw [zipIdx_aux B.reverse (fun a k => C (a : ZMod P) * X ^ (k + 1)) 0, List.length_reverse]

open Polynomial in
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

open Polynomial in
/-- Coefficient at a degree `> |B|` is zero. -/
theorem msgPoly_coeff_high (B : List Nat) (d : Nat) (hd : B.length < d) :
    (msgPoly B).coeff d = 0 := by
  rw [msgPoly_coeff, if_neg (by omega)]

open Polynomial in
/-- Coefficient at degree `k+1` (for `k < |B|`) is the reverse-indexed block. -/
theorem msgPoly_coeff_succ (B : List Nat) (k : Nat) (hk : k < B.length) :
    (msgPoly B).coeff (k + 1)
      = ((B.reverse[k]'(by rwa [List.length_reverse]) : Nat) : ZMod P) := by
  rw [msgPoly_coeff, if_pos (by omega)]
  simp only [Nat.add_sub_cancel]
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_reverse])]

/-- `msgPoly B` has degree at most the block count. -/
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

/-- **Distinct messages ⇒ distinct polynomials.** With field-element, nonzero
    blocks, `B ≠ B'` forces `msgPoly B ≠ msgPoly B'`: either a length mismatch
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

    The crown jewel. Over the prime field `ZMod P`, two distinct messages (as
    field-element, nonzero block lists) collide under Poly1305 for at most
    `max |B| |B'|` choices of the key component `r`. This is the
    information-theoretic guarantee behind Poly1305's unforgeability: a value `r`
    causing a collision is a root of the nonzero difference polynomial, and a
    degree-`n` polynomial over a field has at most `n` roots.

    `ZMod P` is a field exactly when `P` is prime; `P = 2¹³⁰ − 5` is the Poly1305
    prime. Its 40-digit primality is taken as the hypothesis `[Fact P.Prime]`
    rather than discharged here (that needs a Pratt certificate). -/
open Polynomial in
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

/-! ## Lifting the bound to messages

    `toBlocks` outputs exactly the field-element, nonzero blocks the bound needs,
    so the hypotheses of `poly1305_almost_universal` are automatic for any
    message. -/

/-- Every block produced by `toBlocks` is a nonzero field element: full blocks
    carry the `2¹²⁸` high bit, the final block the `2^(8·len)` bit. -/
private theorem goPos (bs : List UInt8) : ∀ b ∈ toBlocks.go bs, 0 < b ∧ b < P := by
  induction bs using toBlocks.go.induct with
  | case1 => intro b hb; simp [toBlocks.go] at hb
  | case2 bs hne _block _rest hlen ih =>
    rw [go_cons bs hne, dif_pos hlen]
    intro b hb
    rcases List.mem_cons.mp hb with h | h
    · subst h
      have hge := blockToNat_ge (bs.take 16) hlen
      exact ⟨by omega, blockToNat_lt_P _ hlen⟩
    · exact ih b h
  | case3 bs hne _block hlen =>
    rw [go_cons bs hne, dif_neg hlen]
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    refine ⟨?_, finalBlockToNat_lt_P _ (List.length_take_le 16 bs)⟩
    unfold finalBlockToNat
    have : 0 < 2 ^ ((bs.take 16).length * 8) := by positivity
    omega

/-- Every `toBlocks` block is a nonzero field element (`0 < b < P`). -/
theorem toBlocks_pos (msg : List UInt8) : ∀ b ∈ toBlocks msg, 0 < b ∧ b < P := by
  unfold toBlocks; exact goPos msg

open Polynomial in
/-- **Message-level forgery bound.** For two messages whose block expansions
    differ, the Poly1305 polynomials collide for at most `max #blocks` keys
    `r : ZMod P`. (Lifting the `toBlocks M ≠ toBlocks M'` hypothesis to
    `M ≠ M'` is `toBlocks_inj`, the remaining gap.) -/
theorem poly1305_almost_universal_msg [Fact (Nat.Prime P)] (M M' : List UInt8)
    (hne : toBlocks M ≠ toBlocks M') :
    (Finset.univ.filter (fun r : ZMod P =>
      (msgPoly (toBlocks M)).eval r = (msgPoly (toBlocks M')).eval r)).card
      ≤ max (toBlocks M).length (toBlocks M').length :=
  poly1305_almost_universal (toBlocks M) (toBlocks M') (toBlocks_pos M) (toBlocks_pos M') hne

end Poly1305.Spec
