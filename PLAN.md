# Development history — the path taken

This is a retrospective of how `lean-chacha-poly` reached its current state. For *what*
is proved and *how to use it*, see [`README.md`](README.md). The project is complete:
`lake build` is `sorry`-free, the RFC 8439 vectors pass, and the capstones are
axiom-clean (modulo one documented `bv_decide` axiom).

> **Correction to the original scope.** The first design notes described this as an
> "axiom-free, Mathlib-free" project with security "out of scope." That turned out to be
> too pessimistic: the Poly1305 *information-theoretic* security results **are** provable
> in Lean and now form the centerpiece (using Mathlib's `Polynomial`/`ZMod`). The only
> non-foundational axiom is the `bv_decide` SAT-certificate behind the quarter-round
> bijection.

## Stage 1 — Functional correctness

Defined the three primitives over `List UInt8` and proved the functional capstones:

- ChaCha20: keystream-length correctness + XOR cancellation ⇒ `chacha20_involutive`
  (encrypt = decrypt) and `chacha20_length`.
- AEAD: `decrypt_encrypt` (the roundtrip) by algebraic assembly — `encrypt` emits
  `ct ‖ tag`, `decrypt` splits it, recomputes the same tag, and re-applies the ChaCha20
  involution.
- **Native bridges** (since removed): a `ByteArray` wrapper per primitive with
  `*_eq_spec` theorems. An external audit later found these definitional — the wrapper
  *was* the spec, so the bridge theorems were tautologies — and the layer was deleted
  (see Stage 5). A real implementation-equivalence theorem awaits an independently
  written fast implementation.

Validated against the RFC 8439 test vectors (`Tests/`).

## Stage 2 — Information-theoretic security (the centerpiece)

Built the Poly1305 unforgeability argument as a tower:

1. `accumulate_eq_poly` — the iterative MAC loop equals polynomial evaluation in
   `GF(P)`, `P = 2¹³⁰ − 5` (`Spec/Accumulate.lean`).
2. `accumulate_cast_eq_eval` — recast in `ZMod P`: the accumulator is `(msgPoly B).eval r`.
3. `poly1305_almost_universal` — over the field, two distinct block-lists collide for at
   most `max #blocks` keys `r`, because a colliding `r` is a root of a nonzero difference
   polynomial and a degree-`n` polynomial has ≤ `n` roots (`Polynomial.card_roots'`).
   Field-ness needs `P` prime, taken as `[Fact (Nat.Prime P)]`.
4. `poly1305_almost_delta_universal` + `collision_union_bound` + the ≤ 8 candidate count
   ⇒ `poly1305_byte_forgery`: the real byte-level bound `8·⌈L/16⌉`.
5. `clampImage_card` (`Spec/Clamp.lean`): the clamp mask leaves `128 − 22 = 106` bits
   free, so the clamped key space has exactly `2¹⁰⁶` elements (a bit-counting bijection
   between submasks and Boolean assignments to the free bits). Dividing the byte-level
   count by it gives `poly1305_clamped_forgery_prob`: the published forgery probability
   `8⌈L/16⌉ / 2¹⁰⁶`.
6. `Injectivity.lean`: the `2^(8·len)` padding makes the byte→block encoding injective
   (`leVal_inj → blockToNat_inj/finalBlockToNat_inj → toBlocks_inj`), lifting the bound
   to distinct *messages*.

On the AEAD side: `decrypt_verifies` (verify-before-decrypt) and `macData_inj` /
`*_binding` (the RFC §2.8 length-framed MAC input is injective in `(aad, ciphertext)`).

## Stage 3 — Subtype standardization

Replaced three inconsistent ways of carrying length invariants (structures-with-proofs,
threaded proof parameters, and unchecked `!`-indexing) with one: `{ x // p x }` subtypes
in `Subtypes.lean` (`Bytes n`, `Words n`, `Padded`). `State` became `Words 16` with
*total* `get`/`set` (no panicking indexing); keys/blocks/tags/MAC-input carry their
length in the type. The analytic security tower was preserved behind a `blockNats` /
`toBlockNats` adapter so the migration didn't disturb the axiom-clean proofs.

## Stage 4 — Finalization

- **Reorg.** Surfaced capstone-grade results at each primitive's top level
  (`Correctness.lean` for functional correctness, `Security.lean` / `Injectivity.lean`
  for security), with supporting lemmas under `<Primitive>/Spec/`. Eliminated the
  "declared in Spec, proved elsewhere" split and the empty `Block.lean`.
- **Dedup / prune.** One shared `foldl_add_eq_sum` (was copied 4×); removed `rfl` no-op
  lemmas and unused characterizations.
- **Comments.** Every significant theorem tagged `**Capstone**` / `**Key lemma**` /
  `**Supporting**`; purged stale prose (the old "Mathlib-free / remaining gap / out of
  scope" notes).
- **Docs.** This file and a full `README.md`, including an honest "what is NOT covered"
  section.

## Stage 5 — Audit response

An external audit (2026-06-10) verified the headline claims but found the security
theorems stopped at the *accumulator* (the "s cancels" step was prose), the Native
bridges were definitional tautologies, and the Poly1305/AEAD towers never met.
Addressed in full:

- **Tag-level forgery theorem** (`poly1305_tag_forgery`, `_prob`): about the real
  `poly1305` and real 16-byte tags; subtracting two tag equations (via
  `poly1305_value`) cancels the one-time pad `s` inside Lean. Bounds stated literally
  as `8 · max ⌈|M|/16⌉ ⌈|M'|/16⌉` via the new `toBlockNats_length`.
- **The towers meet** (`aead_forgery_bound`, `aead_forgery_prob` in `Aead/Security`):
  `macData_inj` + the tag-level theorem give the AEAD forgery probability under the
  uniform-poly-key model hypothesis (= the ChaCha20-PRF idealization);
  `decrypt_accepts` ties acceptance to the counted tag equation.
- **Probability model closed** (`clamp_fiber_card`): every clamped value has exactly
  `2²²` preimages, so uniform 16-byte `r` through `clamp` is uniform on the clamped
  keys. The counting machinery was generalized (`bitConstrained_card`) to serve both
  this and `clampImage_card`.
- **Native layer deleted** (see Stage 1's note) — the wrappers were the spec itself,
  so the `*_eq_spec` theorems stated nothing.
- **Pruned** a dozen contentless declarations (rfl-grade restatements, generic facts
  in crypto costume, one-line contrapositives); `clamp_rfc` strengthened to a complete
  characterization (cleared bits false **and** all other bits preserved).
- **Hygiene**: `Tests/AxiomGuard.lean` (`#guard_msgs` on `#print axioms` — the build
  fails if a capstone's axiom set grows), GitHub Actions CI, `.gitignore`.

## Current structure

```
LeanChachaPoly/
  Subtypes.lean
  ChaCha20/   Spec · Correctness             + Spec/{QuarterRound,Keystream,Seek,Permutation,Xor}
  Poly1305/   Spec · Security · Injectivity  + Spec/{Sum,Blocking,Accumulate,Tag,Clamp}
  Aead/       Spec · Correctness · Security  + Spec/{KeyDerivation,MacData}
Tests/        ChaCha20Test · Poly1305Test · ChaCha20Poly1305Test · PropertiesTest · AxiomGuard · Helpers
```

## Verification

- `lake build` — 0 `sorry`.
- `Tests/AxiomGuard.lean` — `#guard_msgs`-enforced `#print axioms` on every capstone:
  `{propext, Classical.choice, Quot.sound}`, plus the pre-existing
  `quarterRound …bv_decide.ax` pair (the lone non-foundational axiom). The build fails
  if any set grows.
- `lake exe test` — all RFC 8439 vector groups + property checks pass.
- CI (`.github/workflows/ci.yml`) runs all of the above on every push.

## Future work

- **Drop the last axiom.** Reprove the quarter-round round-trips algebraically (from
  `rotl32_inv` / `rotl32_xor` / `xor_self_cancel`) instead of `bv_decide`, making the
  whole library uniformly foundational.
- **Unconditional security.** Discharge `Nat.Prime (2¹³⁰ − 5)` via a Pratt certificate,
  removing the `[Fact (Nat.Prime P)]` hypothesis.
