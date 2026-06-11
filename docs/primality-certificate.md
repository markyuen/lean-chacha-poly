# Primality of `2¹³⁰ − 5` — the axiom-free certificate

The field-level Poly1305 bounds need `ZMod P` to be a field, i.e. `P = 2¹³⁰ − 5`
prime. `LeanChachaPoly/Poly1305/Spec/Primality.lean` discharges this as
`Poly1305.Spec.prime_P : Nat.Prime P` and provides `instance : Fact (Nat.Prime P)`,
which the security theorems resolve directly — they carry no primality hypothesis
and are unconditional.

## Axiom-free, via kernel `decide` on a fuel-based `powMod`

The certificate adds **no axiom** beyond the three foundational ones (`#print
axioms prime_P` → `[propext, Classical.choice, Quot.sound]`); the axiom guard
pins this. The key is that the Lucas certificate's modular exponentiations are
evaluated by the **Lean kernel** through a fuel-based binary `powMod` and plain
`decide` — *not* `native_decide`, so there is no `Lean.ofReduceBool` compiler-trust
axiom.

This works because the kernel reduces `Nat.mul`, `Nat.mod`, `Nat.div` on literals
with GMP, so ~130 modular squarings are milliseconds of kernel work. The thing
that is infeasible to kernel-reduce is `ZMod`'s generic `^` (`Monoid.npow` is
linear in the exponent); routing through `powMod` avoids it. `cast_powMod` bridges
`powMod` back to `ZMod` powers (`(↑(powMod b e m fuel) : ZMod m) = (↑b)^e` when
`e < 2^fuel`), so the `decide`-checked Nat facts feed `lucas_primality`.

## Structure (`Primality.lean`)

- `powMod` / `powMod_lt` / `cast_powMod` — the kernel-evaluable modpow and its
  `ZMod` bridge.
- `prime_divisor_mem` — a prime dividing a product of primes is one of them,
  reducing `lucas_primality`'s universal-over-prime-divisors to the explicit
  factor list.
- `prime_of_powMod` — the assembler: from `1 < p`, `p-1 = qs.prod`, each `qs`
  entry prime, `powMod a (p-1) p 200 = 1`, and `powMod a ((p-1)/q) p 200 ≠ 1` per
  factor (all by `decide`), conclude `Nat.Prime p`.
- One `prime_<value>` per node of the factor tree, bottom-up (`2`, `3` by
  `Nat.prime_two`/`three`), culminating in `prime_P`.

`maxRecDepth` is raised (the `decide` reductions recurse to fuel depth 200).

## The factor tree and witnesses

`P − 1 = 2¹³⁰ − 6 = 2 · 23 · 32985101 · 897064739519922787230182993783`.

Each line: prime, its Lucas witness `g` (a primitive root), and the factorization
of `prime − 1`. Post-order, so every factor is certified before use.

```
2                                          g=1
3                                          g=2   2: 2
5                                          g=2   4: 2^2
7                                          g=3   6: 2 · 3
11                                         g=2   10: 2 · 5
13                                         g=2   12: 2^2 · 3
17                                         g=3   16: 2^4
23                                         g=5   22: 2 · 11
43                                         g=3   42: 2 · 3 · 7
47                                         g=5   46: 2 · 23
67                                         g=2   66: 2 · 3 · 11
73                                         g=5   72: 2^3 · 3^2
89                                         g=3   88: 2^3 · 11
109                                        g=6   108: 2^2 · 3^3
461                                        g=2   460: 2^2 · 5 · 23
487                                        g=3   486: 2 · 3^5
881                                        g=3   880: 2^4 · 5 · 11
4889                                       g=3   4888: 2^3 · 13 · 47
19403                                      g=2   19402: 2 · 89 · 109
37003                                      g=2   37002: 2 · 3 · 7 · 881
221101                                     g=22  221100: 2^2 · 3 · 5^2 · 11 · 67
3134801                                    g=3   3134800: 2^4 · 5^2 · 17 · 461
32985101                                   g=2   32985100: 2^2 · 5^2 · 17 · 19403
4024685905107147541                        g=2   …: 2^2 · 3^2 · 5 · 13 · 43 · 4889 · 37003 · 221101
897064739519922787230182993783             g=5   …: 2 · 73 · 487 · 3134801 · 4024685905107147541
1361129467683753853853498429727072845819   g=2   P−1: 2 · 23 · 32985101 · 897064739519922787230182993783
```

(The last line is `P = 2¹³⁰ − 5`.) Factorizations were obtained by Pollard-rho;
each cofactor is certified recursively by the tree above. `Primality.lean` is
generated from this data.
