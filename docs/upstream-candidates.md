# Upstream candidates

This repo proves a number of small `List`/`ByteArray` lemmas for the bridge.
Checked against Lean core v4.29.1 (this repo's toolchain) and Mathlib v4.29.1,
one is general enough to upstream; the rest are already in core or a one-step
composition of core lemmas, and are recorded below so they are not re-filed.

## `bitConstrained_card` → Mathlib

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
prescribed by `v` number exactly `2 ^ (#¬Q)`. Combinatorics over `Finset.range`
and `Nat.testBit` with no crypto context; the proof bijects such numbers with
bit-assignments via `Finset.card_nbij'`.

No analogue found in Mathlib: a search for a `filter … testBit … card` or
`2 ^ (… filter … card)` bit-counting statement returns nothing. Home would be
`Mathlib.Data.Nat.Bits`. Drop the `private` and generalize the docstring on the
way up.

## Already in core — not candidates

Each of these is a project-local name for a fact core already proves, or a short
composition of core lemmas. Listed with the core lemmas that subsume them.

**`zipWith_take_right`** in
[`LeanChachaPoly/Fast/Bridge/ChaCha20.lean`](../LeanChachaPoly/Fast/Bridge/ChaCha20.lean)
(`zipWith f l (l₂.take l.length) = zipWith f l l₂`). Its general form is core's
`List.zipWith_eq_zipWith_take_min`, from which the right-take shape follows in
three lines (two `rw`, one `simp [List.length_take, List.take_take]`). The repo
proves it by direct induction instead; a local choice, not a missing fact.

**The `ByteArray ↔ List` kit** in
[`LeanChachaPoly/Fast/Bridge/ByteList.lean`](../LeanChachaPoly/Fast/Bridge/ByteList.lean).
The bridge rewrites through `b.data.toList`; core proves the facts that path
needs one layer lower, on `.data` (the `Array`): `data_push`, `data_append`,
`data_extract`, `size_data`, `getElem_eq_getElem_data`, `List.data_toByteArray`,
`List.toByteArray_inj` (in `Init/Data/ByteArray/{Basic,Bootstrap,Lemmas}.lean`).
Each `ByteList` lemma composes one of those with the matching `Array.toList_*`
lemma to land on `(·.data.toList)` under one name — bare `simp` closes the same
goals from core alone. `append` and `toByteArray` are already core in the
`(·.data.toList)` shape (`ByteArray.toList_data_append`,
`List.toList_data_toByteArray`).

**Splice/segment helpers** (`set4_splice`, `zipWith_seg`, `take_set_succ`) in
[`LeanChachaPoly/Fast/Bridge/ChaCha20.lean`](../LeanChachaPoly/Fast/Bridge/ChaCha20.lean).
The core `List` splice/segment API already exists — `set_eq_take_append_cons_drop`,
`take_set`, `take_add_one`, `set_eq_of_length_le`, `getElem?_set_self`,
`zipWith_append`, `take_add`, `drop_drop` — and these helpers are
compositions of it: `take_set_succ`'s proof composes `take_add_one`,
`take_set`, `set_eq_of_length_le`, and `getElem?_set_self`; `zipWith_seg`'s own proof is
`rw [take_add, drop_drop, zipWith_append]`; `set4_splice` iterates
`set_eq_take_append_cons_drop` four times. Project-specific shapes over an
existing API, so they stay local.
