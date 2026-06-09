import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.ChaCha20.Spec.Block
import LeanChachaPoly.ChaCha20.Spec.Xor

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

/-! ## Counter independence

    `keystream_counter_shift` (CTR seekability) is proved in
    `ChaCha20.Spec.Seek`, which imports Mathlib — kept out of this file so the
    capstone chain (`chacha20_involutive`/`chacha20_length`, below) stays
    Mathlib-free. It keeps the `ChaCha20.Spec.*` qualified name. -/

/-! ## Capstones C1 & C2 (declared in `ChaCha20.Spec`)

    These are stated in `ChaCha20.Spec` but proved here, where both
    `keystream_length` and the `xorBytes` lemmas are in scope. Being in the
    same namespace, they carry the `ChaCha20.Spec.*` qualified name. -/

/-- C2: ChaCha20 preserves message length. -/
theorem chacha20_length (key : Key) (nonce : Nonce)
    (counter : UInt32) (msg : List UInt8) :
    (chacha20 key nonce counter msg).length = msg.length := by
  unfold chacha20
  rw [xorBytes_length, keystream_length, Nat.min_self]

/-- C1: ChaCha20 is an involution — encrypting twice returns the message. -/
theorem chacha20_involutive (key : Key) (nonce : Nonce)
    (counter : UInt32) (msg : List UInt8) :
    chacha20 key nonce counter (chacha20 key nonce counter msg) = msg := by
  have hks : (keystream key nonce counter msg.length).length = msg.length :=
    keystream_length key nonce counter msg.length
  have hxlen : (xorBytes msg (keystream key nonce counter msg.length)).length
      = msg.length := by rw [xorBytes_length, hks, Nat.min_self]
  simp only [chacha20]
  rw [hxlen]
  exact xorBytes_involutive msg (keystream key nonce counter msg.length) hks.symm

end ChaCha20.Spec
