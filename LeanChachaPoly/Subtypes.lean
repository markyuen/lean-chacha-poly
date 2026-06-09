/-!
# Length/size-indexed subtypes

The whole library standardizes its length and size invariants on `Subtype`s written
with `{ x // p x }` syntax, so the invariant is enforced *in the type* rather than
threaded as a proof parameter or trusted through `!`-indexing.

- `Bytes n`  — a `List UInt8` of exactly `n` bytes (keys, nonces, blocks, tags, …).
- `Words n`  — an `Array UInt32` of exactly `n` words (the ChaCha20 `State`).
- `Padded`   — a `List UInt8` whose length is a multiple of 16 (Poly1305 MAC input).

`Words.get`/`Words.set` are *total* indexed operations (no `Array.get!`/`set!`): the
size invariant in the type discharges the bounds proof, so out-of-range access is
impossible by construction.

This file is intentionally `Mathlib`-free — it depends only on core `Array`/`Subtype`.
-/

/-- A list of exactly `n` bytes. -/
abbrev Bytes (n : Nat) := { l : List UInt8 // l.length = n }

/-- An array of exactly `n` 32-bit words. -/
abbrev Words (n : Nat) := { a : Array UInt32 // a.size = n }

/-- A byte list whose length is a multiple of 16. -/
abbrev Padded := { l : List UInt8 // l.length % 16 = 0 }

namespace Words

/-- Total indexed read: the size invariant discharges the bounds obligation. -/
def get {n : Nat} (s : Words n) (i : Fin n) : UInt32 :=
  s.val[i.val]'(by rw [s.property]; exact i.isLt)

/-- Total indexed write: preserves the size invariant by construction. -/
def set {n : Nat} (s : Words n) (i : Fin n) (x : UInt32) : Words n :=
  ⟨s.val.set i.val x (by rw [s.property]; exact i.isLt),
   by rw [Array.size_set]; exact s.property⟩

end Words
