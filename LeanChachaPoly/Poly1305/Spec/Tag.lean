import LeanChachaPoly.Poly1305.Spec
import LeanChachaPoly.Poly1305.Spec.Sum
import Mathlib

/-!
# Poly1305 Tag Finalization

The tag is `(accumulate + s) mod 2¹²⁸`, serialized to 16 bytes. `poly1305_value`
shows the serialization is faithful (the tag *is* the reduced value), which is
what lets `Poly1305.Security.poly1305_tag_forgery` reason about actual tag bytes:
subtracting two tag equations cancels the one-time pad `s` exactly.
-/

namespace Poly1305.Spec

/-! ## Serialization round-trip -/

/-- Base-`b` reconstruction: summing the first `k` little-endian base-`b` digits,
    weighted by their place value, recovers any `x < b^k`. -/
private theorem digitSum (b : Nat) (hb : 0 < b) :
    ∀ k x, x < b ^ k → (∑ i ∈ Finset.range k, x / b ^ i % b * b ^ i) = x := by
  intro k
  induction k with
  | zero => intro x hx; simp only [pow_zero, Nat.lt_one_iff] at hx; subst hx; simp
  | succ k ih =>
    intro x hx
    rw [Finset.sum_range_succ']
    have hshift : (∑ i ∈ Finset.range k, x / b ^ (i + 1) % b * b ^ (i + 1))
        = b * (x / b) := by
      have hterm : ∀ i ∈ Finset.range k,
          x / b ^ (i + 1) % b * b ^ (i + 1) = b * (x / b / b ^ i % b * b ^ i) := by
        intro i _
        rw [Nat.div_div_eq_div_mul, ← pow_succ', pow_succ]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        ih (x / b) (by rw [Nat.div_lt_iff_lt_mul hb, ← pow_succ]; exact hx)]
    rw [hshift]
    simp only [pow_zero, Nat.div_one, mul_one]
    have := Nat.div_add_mod x b
    omega

/-- **Key lemma.** The serialized tag round-trips: deserializing the 16 little-endian bytes of
    `x` recovers `x`, for any `x < 2¹²⁸`. So the Poly1305 tag is exactly
    `(accumulate + s) mod 2¹²⁸` (fully reduced), not a lossy truncation. -/
theorem leToNat16_natToLe16 (x : Nat) (hx : x < 2 ^ 128) :
    leToNat16 (natToLe16 x) = x := by
  unfold leToNat16
  rw [foldl_add_eq_sum, Nat.zero_add, ← Fin.sum_univ_def]
  have hcongr : ∀ i : Fin 16,
      ((natToLe16 x).val.get (i.cast (natToLe16 x).property.symm)).toNat * 2 ^ (i.val * 8)
        = x / 2 ^ (i.val * 8) % 256 * 2 ^ (i.val * 8) := by
    intro i
    rw [List.get_eq_getElem]
    simp only [natToLe16, List.getElem_map, List.getElem_range, Fin.val_cast,
      Nat.shiftRight_eq_div_pow, UInt8.toNat_ofNat', Nat.reducePow]
    congr 1
    omega
  rw [Finset.sum_congr rfl (fun i _ => hcongr i),
    Fin.sum_univ_eq_sum_range (fun j => x / 2 ^ (j * 8) % 256 * 2 ^ (j * 8)) 16,
    Finset.sum_congr rfl
      (fun j _ => by rw [show (2 : Nat) ^ (j * 8) = 256 ^ j by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul, Nat.mul_comm]])]
  exact digitSum 256 (by norm_num) 16 x (by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul]; exact hx)

/-- **Key lemma.** The tag is fully reduced: reading the 16-byte Poly1305 output back as a
    number gives exactly `(accumulate r blocks + s) mod 2¹²⁸` — the serialization
    loses nothing, so the tag is the true reduced value rather than a truncation. -/
theorem poly1305_value (key : Key) (msg : List UInt8) :
    leToNat16 (poly1305 key msg) =
      (accumulate (extractR key) (blockNats (toBlocks msg)) + extractS key) % 2 ^ 128 := by
  have h : (accumulate (extractR key) (blockNats (toBlocks msg)) + extractS key) % 2 ^ 128
      < 2 ^ 128 := Nat.mod_lt _ (by positivity)
  unfold poly1305
  exact leToNat16_natToLe16 _ h

end Poly1305.Spec
