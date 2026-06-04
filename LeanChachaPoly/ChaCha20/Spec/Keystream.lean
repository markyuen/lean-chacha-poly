import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.ChaCha20.Spec.Block

/-!
# ChaCha20 Keystream Properties

Properties of `keystream`, particularly its length.

## Role in the proof chain

`keystream_length` is the critical lemma that lets us satisfy
the length precondition of `xorBytes_self_cancel` in the
involution proof.

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

/-- Generating n blocks and serializing each gives n×64 bytes. -/
theorem blockStream_length (key : Key) (nonce : Nonce)
    (counter : UInt32) (n : Nat) :
    ((List.range n).flatMap fun i =>
      serializeBlock (chacha20Block key nonce (counter + UInt32.ofNat i))).length
    = n * 64 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp only [List.flatMap_singleton]
    rw [serializeBlock_length _ (chacha20Block_size key nonce _)]
    omega

/-! ## Keystream length -/

/-- The keystream is exactly as long as requested. -/
theorem keystream_length (key : Key) (nonce : Nonce)
    (counter : UInt32) (len : Nat) :
    (keystream key nonce counter len).length = len := by
  simp only [keystream]
  rw [List.length_take, blockStream_length]
  apply Nat.min_eq_left
  omega

/-! ## Counter independence -/

/-- Different counter values produce the keystream for the
    corresponding block offset. This is used when reasoning
    about multi-block messages. -/
theorem keystream_counter_shift (key : Key) (nonce : Nonce)
    (ctr : UInt32) (len offset : Nat) :
    keystream key nonce (ctr + UInt32.ofNat offset) len =
    (keystream key nonce ctr (len + offset * 64)).drop (offset * 64) := by
  sorry

end ChaCha20.Spec
