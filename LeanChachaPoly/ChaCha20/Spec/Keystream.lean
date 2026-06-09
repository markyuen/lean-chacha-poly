import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.ChaCha20.Spec.Xor

/-!
# ChaCha20 Keystream Properties

Properties of `keystream`, particularly its length.

## Role in the proof chain

`keystream_length` is the lemma that lets `chacha20_involutive`
(in `ChaCha20.Correctness`) satisfy the equal-length precondition
of `xorBytes_involutive`.

The proof reduces to:
  - We generate ⌈len/64⌉ blocks of 64 bytes each
  - We flatMap them together (total = ⌈len/64⌉ × 64 bytes ≥ len)
  - We take the first `len` bytes

The key arithmetic: `(List.flatMap ... serializeBlock).length = nBlocks * 64`,
and `(stream.take len).length = min len stream.length = len`
when `stream.length ≥ len`.
-/

namespace ChaCha20.Spec

/-! ## Block list length -/

/-- **Supporting.** Generating n blocks and serializing each gives n×64 bytes. -/
theorem blockStream_length (key : Key) (nonce : Nonce)
    (counter : UInt32) (n : Nat) :
    ((List.range n).flatMap fun i =>
      (serializeBlock (chacha20Block key nonce (counter + UInt32.ofNat i))).val).length
    = n * 64 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp only [List.flatMap_singleton]
    rw [(serializeBlock (chacha20Block key nonce (counter + UInt32.ofNat n))).property]
    omega

/-! ## Keystream length -/

/-- **Key lemma.** The keystream is exactly as long as requested. -/
theorem keystream_length (key : Key) (nonce : Nonce)
    (counter : UInt32) (len : Nat) :
    (keystream key nonce counter len).length = len := by
  simp only [keystream]
  rw [List.length_take, blockStream_length]
  apply Nat.min_eq_left
  omega

/-! `keystream_length` feeds the `chacha20_length` / `chacha20_involutive` capstones in
    `ChaCha20.Correctness`; CTR seekability (`keystream_counter_shift`) is in
    `ChaCha20.Spec.Seek`. -/

end ChaCha20.Spec
