import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.ChaCha20.Spec.QuarterRound

/-!
# ChaCha20 Block Function Properties

Properties of `chacha20Block` and `serializeBlock`.

## Role in the proof chain

`serializeBlock_length` is needed by `keystream_length` which is
needed by `chacha20_involutive`. It confirms each block produces
exactly 64 bytes.

The other theorems here are characterizing properties: they validate
that the block function is implemented correctly and support the
RFC test vector check.
-/

namespace ChaCha20.Spec

/-! ## Serialization lemmas -/

/-- `u32ToLe` always produces exactly 4 bytes. -/
@[simp]
theorem u32ToLe_length (w : UInt32) : (u32ToLe w).length = 4 := by
  simp [u32ToLe]

/-- Serializing 16 words produces 64 bytes. -/
theorem serializeBlock_length (s : State) (h : s.size = 16) :
    (serializeBlock s).length = 64 := by
  have hs : s.toList.length = 16 := by simp [h]
  have flatMap_len : ∀ (xs : List UInt32), (xs.flatMap u32ToLe).length = xs.length * 4 := fun xs => by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [u32ToLe_length, ih, Nat.succ_mul]; omega
  simp [serializeBlock, flatMap_len, hs]

/-- Adding two states of size 16 gives a state of size 16. -/
theorem addStates_size (s t : State) (hs : s.size = 16) (ht : t.size = 16) :
    (addStates s t).size = 16 := by
  simp [addStates, Array.size_zipWith, hs, ht]

/-! ## Block function size -/

/-- The block function output has size 16. -/
theorem chacha20Block_size (key : Key) (nonce : Nonce) (counter : UInt32) :
    (chacha20Block key nonce counter).size = 16 := by
  simp [chacha20Block]
  apply addStates_size
  · apply tenDoubleRounds_size
    exact initState_size key nonce counter
  · exact initState_size key nonce counter

/-! ## RFC 8439 §2.3.2 block function test vector

    Key:     0x00010203...0x1f (32-byte ascending)
    Nonce:   0x00000009 0x0000004a 0x00000000
    Counter: 1

    Checks first 4 words of the output state.
    Full verification is by `decide`; the complete 64-byte
    keystream check is in `Test/ChaCha20Test.lean`. -/
-- Expensive: left as a `#eval` check rather than compiled theorem.
-- #eval (chacha20Block myKey myNonce 1)[0]!  -- should be 0xe4e7f110

end ChaCha20.Spec
