import LeanChachaPoly.Poly1305.Spec

/-!
# Poly1305 Native — ByteArray Bridge

Bridges the `List UInt8`-based spec to `ByteArray`.
-/

namespace Poly1305.Native

open Poly1305.Spec

/-- Compute Poly1305 tag over a ByteArray message. -/
def poly1305 (key : Key) (msg : ByteArray) : ByteArray :=
  ByteArray.mk (Spec.poly1305 key msg.data.toList).toArray

/-! ## Bridge theorem -/

theorem poly1305_eq_spec (key : Key) (msg : ByteArray) :
    (poly1305 key msg).data.toList =
      Spec.poly1305 key msg.data.toList := by
  simp [poly1305, Array.toList_toArray]

/-! ## Derived properties -/

theorem poly1305_size (key : Key) (msg : ByteArray) :
    (poly1305 key msg).size = 16 := by
  simp [poly1305, ByteArray.size, Array.size_toArray,
        List.length_toArray, Spec.poly1305_length]

end Poly1305.Native
