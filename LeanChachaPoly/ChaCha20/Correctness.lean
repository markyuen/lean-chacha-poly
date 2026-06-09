import LeanChachaPoly.ChaCha20.Spec.Keystream
import LeanChachaPoly.ChaCha20.Spec.Xor

/-!
# ChaCha20 Correctness

The two top-level correctness guarantees for the stream cipher, assembled from the
keystream-length and XOR-cancellation lemmas:

- `chacha20_length` — encryption preserves message length.
- `chacha20_involutive` — encryption is its own inverse (encrypt = decrypt), the
  fundamental correctness property of a XOR stream cipher.

(The structural companion `quarterRound_bijective` lives in `Spec/Permutation.lean`.)
-/

namespace ChaCha20.Spec

/-- **Capstone.** ChaCha20 preserves message length. -/
theorem chacha20_length (key : Key) (nonce : Nonce)
    (counter : UInt32) (msg : List UInt8) :
    (chacha20 key nonce counter msg).length = msg.length := by
  unfold chacha20
  rw [xorBytes_length, keystream_length, Nat.min_self]

/-- **Capstone.** ChaCha20 is an involution — encrypting twice returns the message,
    so encryption and decryption are the same operation. -/
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
