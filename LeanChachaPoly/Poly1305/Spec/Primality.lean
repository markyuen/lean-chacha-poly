import Mathlib.NumberTheory.LucasPrimality
import LeanChachaPoly.Poly1305.Spec

/-!
# Primality of `P = 2¹³⁰ − 5`

A Lucas/Pratt certificate discharging `Nat.Prime (2¹³⁰ − 5)`, the Poly1305 prime,
so the field-level security bounds become unconditional. The certificate is
**axiom-free**: the modular exponentiations are evaluated by the Lean kernel's
GMP-backed `Nat` arithmetic through a fuel-based binary `powMod` and plain
`decide` — no `native_decide`, no compiler-trust axiom (`#print axioms` reports
only the three foundational axioms wherever this is used).

`lucas_primality` reduces primality of `p` to: a witness `a` (a primitive root)
with `a^(p-1) = 1` and `a^((p-1)/q) ≠ 1` for every prime `q ∣ p-1`. The universal
over prime divisors is discharged by `prime_divisor_mem` against the explicit
factor list; `cast_powMod` bridges the kernel-evaluated `powMod` to `ZMod p`
powers. The ~25 primes of the recursive factor tree are certified bottom-up.

See `docs/primality-certificate.md` for the factor tree and witnesses.
-/

set_option maxRecDepth 16000

namespace Poly1305.Spec.Primality

/-- Fuel-based binary modular exponentiation: `powMod b e m fuel = b^e % m`
    whenever `e < 2^fuel`. The recursion is structural in `fuel`, so the kernel
    reduces it through GMP `Nat` arithmetic — `decide` evaluates it at 130-bit
    scale in milliseconds. -/
def powMod (b e m : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | fuel + 1 =>
    if e = 0 then 1 % m
    else if e % 2 = 0 then powMod (b * b % m) (e / 2) m fuel
    else powMod (b * b % m) (e / 2) m fuel * b % m

theorem powMod_lt {m : ℕ} (hm : 0 < m) : ∀ (b e fuel : ℕ), powMod b e m fuel < m
  | b, e, 0 => Nat.mod_lt _ hm
  | b, e, fuel + 1 => by
    rw [powMod]
    split
    · exact Nat.mod_lt _ hm
    · split
      · exact powMod_lt hm (b * b % m) (e / 2) fuel
      · exact Nat.mod_lt _ hm

/-- `powMod` agrees with `ZMod` exponentiation: its cast into `ZMod m` is the
    `ZMod` power. Proved by induction on `fuel`; the `% m` operations vanish under
    `ZMod.natCast_mod`. -/
theorem cast_powMod (m b : ℕ) : ∀ (fuel e : ℕ), e < 2 ^ fuel →
    ((powMod b e m fuel : ℕ) : ZMod m) = (b : ZMod m) ^ e
  | 0, e, he => by
    have h0 : e = 0 := Nat.lt_one_iff.mp (by simpa using he)
    subst h0; simp [powMod, ZMod.natCast_mod]
  | fuel + 1, e, he => by
    rw [powMod]
    by_cases h0 : e = 0
    · subst h0; simp [ZMod.natCast_mod]
    · rw [if_neg h0]
      have he2 : e / 2 < 2 ^ fuel := by
        have h := he; rw [pow_succ] at h; omega
      have ih := cast_powMod m (b * b % m) fuel (e / 2) he2
      by_cases h2 : e % 2 = 0
      · rw [if_pos h2, ih, ZMod.natCast_mod, Nat.cast_mul, ← pow_two, ← pow_mul]
        congr 1; omega
      · rw [if_neg h2]
        rw [ZMod.natCast_mod, Nat.cast_mul, ih, ZMod.natCast_mod, Nat.cast_mul,
          ← pow_two, ← pow_mul, ← pow_succ]
        congr 1; omega

/-- A prime dividing a product of primes is one of them. Reduces the
    `lucas_primality` universal-over-prime-divisors to the explicit factor list. -/
theorem prime_divisor_mem : ∀ (qs : List ℕ), (∀ x ∈ qs, Nat.Prime x) →
    ∀ {q : ℕ}, Nat.Prime q → q ∣ qs.prod → q ∈ qs
  | [], _, q, hq, hd => by
    simp only [List.prod_nil] at hd
    exact absurd (Nat.dvd_one.mp hd) hq.ne_one
  | p :: ps, hall, q, hq, hd => by
    simp only [List.prod_cons] at hd
    rcases (hq.dvd_mul).mp hd with h | h
    · exact List.mem_cons.mpr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (hall p (List.mem_cons_self ..))).mp h))
    · exact List.mem_cons.mpr (Or.inr
        (prime_divisor_mem ps (fun x hx => hall x (List.mem_cons_of_mem _ hx)) hq h))

/-- The certificate assembler: from kernel-checked `powMod` facts plus the factor
    list (each entry prime, product `= p-1`), conclude `Nat.Prime p`. -/
theorem prime_of_powMod (p a : ℕ) (qs : List ℕ)
    (hp1 : 1 < p) (hsize : p - 1 < 2 ^ 200)
    (hqs : ∀ x ∈ qs, Nat.Prime x)
    (hfact : p - 1 = qs.prod)
    (hferm : powMod a (p - 1) p 200 = 1)
    (hnd : ∀ q ∈ qs, powMod a ((p - 1) / q) p 200 ≠ 1) :
    Nat.Prime p := by
  have hp0 : 0 < p := by omega
  apply lucas_primality p (a : ZMod p)
  · rw [← cast_powMod p a 200 (p - 1) hsize, hferm, Nat.cast_one]
  · intro q hqp hqd
    have hmem : q ∈ qs := prime_divisor_mem qs hqs hqp (hfact ▸ hqd)
    intro hc
    apply hnd q hmem
    have hlt : (p - 1) / q < 2 ^ 200 := lt_of_le_of_lt (Nat.div_le_self _ _) hsize
    have hcast := cast_powMod p a 200 ((p - 1) / q) hlt
    have hw : (↑(powMod a ((p - 1) / q) p 200) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [hcast, hc, Nat.cast_one]
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hw
    rwa [Nat.mod_eq_of_lt (powMod_lt hp0 a _ 200), Nat.mod_eq_of_lt hp1] at hmod

theorem p_2 : Nat.Prime 2 := Nat.prime_two
theorem p_3 : Nat.Prime 3 := Nat.prime_three

theorem p_487 : Nat.Prime 487 :=
  prime_of_powMod 487 3 [2, 3, 3, 3, 3, 3]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_73 : Nat.Prime 73 :=
  prime_of_powMod 73 5 [2, 2, 2, 3, 3]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_5 : Nat.Prime 5 :=
  prime_of_powMod 5 2 [2, 2]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_11 : Nat.Prime 11 :=
  prime_of_powMod 11 2 [2, 5]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_5
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_23 : Nat.Prime 23 :=
  prime_of_powMod 23 5 [2, 11]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_11
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_461 : Nat.Prime 461 :=
  prime_of_powMod 461 2 [2, 2, 5, 23]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_5
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_23
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_17 : Nat.Prime 17 :=
  prime_of_powMod 17 3 [2, 2, 2, 2]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_3134801 : Nat.Prime 3134801 :=
  prime_of_powMod 3134801 3 [2, 2, 2, 2, 5, 5, 17, 461]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_5
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_5
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_17
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_461
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_7 : Nat.Prime 7 :=
  prime_of_powMod 7 3 [2, 3]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_43 : Nat.Prime 43 :=
  prime_of_powMod 43 3 [2, 3, 7]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_7
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_881 : Nat.Prime 881 :=
  prime_of_powMod 881 3 [2, 2, 2, 2, 5, 11]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_5
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_11
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_37003 : Nat.Prime 37003 :=
  prime_of_powMod 37003 2 [2, 3, 7, 881]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_7
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_881
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_13 : Nat.Prime 13 :=
  prime_of_powMod 13 2 [2, 2, 3]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_67 : Nat.Prime 67 :=
  prime_of_powMod 67 2 [2, 3, 11]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_11
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_221101 : Nat.Prime 221101 :=
  prime_of_powMod 221101 22 [2, 2, 3, 5, 5, 11, 67]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_5
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_5
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_11
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_67
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_47 : Nat.Prime 47 :=
  prime_of_powMod 47 5 [2, 23]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_23
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_4889 : Nat.Prime 4889 :=
  prime_of_powMod 4889 3 [2, 2, 2, 13, 47]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_13
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_47
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_4024685905107147541 : Nat.Prime 4024685905107147541 :=
  prime_of_powMod 4024685905107147541 2 [2, 2, 3, 3, 5, 13, 43, 4889, 37003, 221101]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_5
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_13
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_43
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_4889
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_37003
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_221101
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_897064739519922787230182993783 : Nat.Prime 897064739519922787230182993783 :=
  prime_of_powMod 897064739519922787230182993783 5 [2, 73, 487, 3134801, 4024685905107147541]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_73
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_487
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3134801
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_4024685905107147541
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_89 : Nat.Prime 89 :=
  prime_of_powMod 89 3 [2, 2, 2, 11]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_11
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_109 : Nat.Prime 109 :=
  prime_of_powMod 109 6 [2, 2, 3, 3, 3]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_3
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_19403 : Nat.Prime 19403 :=
  prime_of_powMod 19403 2 [2, 89, 109]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_89
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_109
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_32985101 : Nat.Prime 32985101 :=
  prime_of_powMod 32985101 2 [2, 2, 5, 5, 17, 19403]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_5
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_5
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_17
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_19403
    · simp at hx)
    (by decide) (by decide) (by decide)

theorem p_1361129467683753853853498429727072845819 : Nat.Prime 1361129467683753853853498429727072845819 :=
  prime_of_powMod 1361129467683753853853498429727072845819 2 [2, 23, 32985101, 897064739519922787230182993783]
    (by decide) (by decide)
    (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_23
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_32985101
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p_897064739519922787230182993783
    · simp at hx)
    (by decide) (by decide) (by decide)

end Poly1305.Spec.Primality

namespace Poly1305.Spec

/-- **The Poly1305 prime is prime.** `2¹³⁰ − 5` is prime, certified axiom-free by
    the Lucas/Pratt tree in `Primality`. Discharges the `[Fact (Nat.Prime P)]`
    hypothesis the security bounds carry. -/
theorem prime_P : Nat.Prime P := by
  show Nat.Prime (2 ^ 130 - 5)
  exact Primality.p_1361129467683753853853498429727072845819

/-- Global instance: every `[Fact (Nat.Prime P)]` security theorem is now
    unconditionally instantiable, with no added axiom. -/
instance : Fact (Nat.Prime P) := ⟨prime_P⟩

end Poly1305.Spec
