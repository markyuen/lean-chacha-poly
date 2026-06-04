import LeanChachaPoly.ChaCha20.Spec

/-!
# XOR Byte-List Lemmas

Properties of `xorBytes` used to prove the ChaCha20 involution.

## Key insight

The entire involution proof reduces to one fact:
`xorBytes (xorBytes msg ks) ks = msg`

This holds because XOR is self-inverse: `(x ^^^ k) ^^^ k = x`
for any byte `x` and key byte `k`. The list version follows
by applying this pointwise via `List.zipWith`.

This is the simplest sub-proof in the entire library.
-/

namespace ChaCha20.Spec

/-! ## UInt8 XOR

    `UInt8.xor_self`, `UInt8.xor_comm`, and `UInt8.xor_assoc` are
    provided by the standard library as `@[simp]` lemmas.
    We add only `xor_cancel` which is needed for the list-level proofs. -/

/-- XOR is its own inverse: (x ^^^ k) ^^^ k = x. -/
@[simp]
theorem UInt8.xor_cancel (x k : UInt8) : (x ^^^ k) ^^^ k = x := by simp [UInt8.xor_assoc]

/-! ## xorBytes properties -/

/-- XOR a list with itself gives all zeros. -/
theorem xorBytes_self (xs : List UInt8) :
    xorBytes xs xs = List.replicate xs.length 0 := by
  induction xs with
  | nil => rfl
  | cons h t ih =>
    simp only [xorBytes] at ih ⊢
    simp only [List.zipWith_cons_cons, UInt8.xor_self, List.length_cons, List.replicate_succ, ih]

/-- xorBytes is symmetric. -/
theorem xorBytes_comm (xs ys : List UInt8) :
    xorBytes xs ys = xorBytes ys xs := by
  unfold xorBytes
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp [List.zipWith_cons_cons, UInt8.xor_comm x y, ih]

/-- xorBytes preserves length (truncates to shorter). -/
theorem xorBytes_length (xs ys : List UInt8) :
    (xorBytes xs ys).length = min xs.length ys.length := by
  simp [xorBytes, List.length_zipWith]

/-- When both lists have the same length, xorBytes length = that length. -/
theorem xorBytes_length_eq (xs ys : List UInt8) (h : xs.length = ys.length) :
    (xorBytes xs ys).length = xs.length := by
  simp [xorBytes_length, h]

/-! ## THE KEY LEMMA

    XOR a list with a keystream, then XOR with the same keystream,
    recovers the original list.

    This is the direct mathematical basis of the involution theorem.
    Proof: pointwise application of `UInt8.xor_cancel`. -/
theorem xorBytes_self_cancel (msg ks : List UInt8) (h : msg.length = ks.length) :
    xorBytes (xorBytes msg ks) ks = msg := by
  induction msg generalizing ks with
  | nil => simp [xorBytes]
  | cons x xs ih =>
    cases ks with
    | nil => simp at h
    | cons k ks =>
      unfold xorBytes
      simp only [List.zipWith_cons_cons, UInt8.xor_cancel]
      unfold xorBytes at ih
      exact congrArg (x :: ·) (ih ks (by simpa using h))

/-- Variant: xorBytes with equal-length lists composed with itself. -/
theorem xorBytes_involutive (msg ks : List UInt8) (h : msg.length = ks.length) :
    xorBytes (xorBytes msg ks) ks = msg :=
  xorBytes_self_cancel msg ks h

end ChaCha20.Spec
