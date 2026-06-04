import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.ChaCha20.Spec.Xor
import LeanChachaPoly.ChaCha20.Spec.Keystream

/-!
# ChaCha20 Native — ByteArray Bridge

Wraps the `List UInt8`-based spec to work with `ByteArray`,
which is what the rest of the library and user code consume.
Proves equivalence, so all Spec theorems transfer automatically.
-/

namespace ChaCha20.Native

open ChaCha20.Spec

/-! ## Key/Nonce constructors from ByteArray -/

def keyFromByteArray (b : ByteArray) (h : b.size = 32) : Key :=
  { bytes := b.data.toList,
    size := by simp [ByteArray.size] at h; simpa [Array.size_toList] using h }

def nonceFromByteArray (b : ByteArray) (h : b.size = 12) : Nonce :=
  { bytes := b.data.toList,
    size := by simp [ByteArray.size] at h; simpa [Array.size_toList] using h }

/-! ## ByteArray operations -/

/-- Encrypt or decrypt a ByteArray message. -/
def chacha20 (key : Key) (nonce : Nonce) (counter : UInt32)
    (msg : ByteArray) : ByteArray :=
  ByteArray.mk (Spec.chacha20 key nonce counter msg.data.toList).toArray

/-- Generate a keystream as ByteArray. -/
def keystream (key : Key) (nonce : Nonce) (counter : UInt32) (len : Nat) : ByteArray :=
  ByteArray.mk (Spec.keystream key nonce counter len).toArray

/-! ## Bridge theorems -/

/-- Native encrypt output length equals input length. -/
theorem chacha20_size (key : Key) (nonce : Nonce) (counter : UInt32)
    (msg : ByteArray) :
    (chacha20 key nonce counter msg).size = msg.size := by
  simp [chacha20, ByteArray.size]
  rw [Array.size_toArray, Spec.chacha20_length]
  simp [ByteArray.size]

/-- Native encrypt equals spec encrypt on toList. -/
theorem chacha20_eq_spec (key : Key) (nonce : Nonce) (counter : UInt32)
    (msg : ByteArray) :
    (chacha20 key nonce counter msg).data.toList =
    Spec.chacha20 key nonce counter msg.data.toList := by
  simp [chacha20, Array.toList_toArray]

/-! ## Derived capstone theorems -/

/-- The involution holds for ByteArray too. -/
theorem chacha20_involutive (key : Key) (nonce : Nonce)
    (counter : UInt32) (msg : ByteArray) :
    chacha20 key nonce counter (chacha20 key nonce counter msg) = msg := by
  apply ByteArray.ext
  rw [chacha20_eq_spec, chacha20_eq_spec]
  · exact Spec.chacha20_involutive key nonce counter msg.data.toList
  · rw [chacha20_size]

end ChaCha20.Native
