# Upstream candidates

Lemmas in this repo that are generic enough to live in Batteries or Mathlib
rather than here. Upstreaming them shrinks the bridge surface (the docs identify
proof churn as the fragile axis) and removes project-local restatements of facts
the ecosystem should own. This file records the candidates and their exact
locations; the PRs themselves are not yet filed.

Before filing any of these, check the current Batteries/Mathlib for an existing
statement — several of these are the kind of lemma that may already have landed
under a different name.

## Priority 1 — `Batteries.Data.ByteArray`

The `ByteArray ↔ List.toList` correspondence lemmas in
[`LeanChachaPoly/Fast/Bridge/ByteList.lean`](../LeanChachaPoly/Fast/Bridge/ByteList.lean).
All are axiom-free and depend only on core Lean + Batteries (no Mathlib); the
rewrite-shaped ones (`toList_push`, `toList_append`, `toList_extract`,
`toList_emptyWithCapacity`, `toList_toByteArray`, `length_toList`) are `@[simp]`:

| Lemma | Statement |
|---|---|
| `toList_push` | `(b.push u).data.toList = b.data.toList ++ [u]` |
| `toList_append` | `(a ++ b).data.toList = a.data.toList ++ b.data.toList` |
| `toList_extract` | `(b.extract s e).data.toList = ((b.data.toList).drop s).take (e - s)` |
| `toList_emptyWithCapacity` | `(ByteArray.emptyWithCapacity n).data.toList = []` |
| `toList_toByteArray` | `l.toByteArray.data.toList = l` |
| `toByteArray_toList` | `b.data.toList.toByteArray = b` |
| `toList_inj` | injectivity of `(·.data.toList)` |
| `length_toList` | `b.data.toList.length = b.size` |
| `getElem_toList` | indexing correspondence |
| `beq_eq_toList_beq` | `(a == b) = (a.data.toList == b.data.toList)` |

Batteries already carries some `ByteArray` API; check for overlap before PRing,
and keep only the lemmas it does not yet have.

## Priority 2 — `Mathlib.Data.Finset.Card` (or `Mathlib.Data.Nat.Bits`)

`bitConstrained_card` in
[`LeanChachaPoly/Poly1305/Spec/Clamp.lean`](../LeanChachaPoly/Poly1305/Spec/Clamp.lean)
(currently `private`):

```lean
theorem bitConstrained_card (N : Nat) (Q : Fin N → Prop) [DecidablePred Q]
    (v : Fin N → Bool) :
    ((range (2 ^ N)).filter (fun x => ∀ i : Fin N, Q i → x.testBit i.val = v i)).card
      = 2 ^ (univ.filter (fun i : Fin N => ¬ Q i)).card
```

The numbers below `2^N` whose bits at the positions satisfying `Q` are
prescribed by `v` number exactly `2 ^ (#¬Q)`. Pure combinatorics over
`Finset.range` and `Nat.testBit` with no crypto context; the proof bijects such
numbers with bit-assignments via `Finset.card_nbij'`. Drop the `private` and
generalize the docstring on the way up.

## Priority 3 — `Batteries.Data.List.ZipWith`

`zipWith_take_right` in
[`LeanChachaPoly/Fast/Bridge/ChaCha20.lean`](../LeanChachaPoly/Fast/Bridge/ChaCha20.lean)
(currently `private`):

```lean
theorem zipWith_take_right {α β γ : Type} (f : α → β → γ) :
    ∀ (l : List α) (l₂ : List β),
      List.zipWith f l (l₂.take l.length) = List.zipWith f l l₂
```

`zipWith` ignores second-list elements beyond the first list's length, so taking
the right operand to the left's length is a no-op. No dependencies beyond
`List.zipWith` / `List.take`.

## Lower priority — splice/segment helpers

Also in [`LeanChachaPoly/Fast/Bridge/ChaCha20.lean`](../LeanChachaPoly/Fast/Bridge/ChaCha20.lean),
useful but born from the byte-stream bridge and needing API design before they
would fit a general home:

- `set4_splice` — four consecutive `List.set` operations compose into a
  take-append-drop splice.
- `zipWith_seg` — splitting `zipWith` over segments.
- `take_set_succ` — `(L.set k v).take (k + 1) = L.take k ++ [v]`.

Check the Batteries `List` roadmap before filing; these may want to be stated in
terms of an existing splice/segment API rather than added piecemeal.
