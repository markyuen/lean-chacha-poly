import LeanChachaPoly.Aead.Spec

/-!
# AEAD Authenticity — structural properties

`decrypt_verifies` is the *verify-before-decrypt* invariant: `decrypt` returns
plaintext only when the received tag matches the tag recomputed over
`(aad, ciphertext)`. There is no control-flow path that releases plaintext on
an authentication failure — the only `some` is guarded by the tag check.
-/

namespace Aead.Spec

open ChaCha20.Spec Poly1305.Spec

/-- **Verify-before-decrypt.** If `decrypt` returns `some _`, then the received
    tag (the last 16 bytes) equals the Poly1305 tag recomputed from the derived
    one-time key over `macData aad ciphertext`. Authentication is checked before
    any plaintext is produced. -/
theorem decrypt_verifies (key : Key) (nonce : Nonce) (ctAndTag aad pt : List UInt8)
    (h : decrypt key nonce ctAndTag aad = some pt) :
    ctAndTag.drop (ctAndTag.length - 16)
      = poly1305 (derivePolyKey key nonce)
          (macData aad (ctAndTag.take (ctAndTag.length - 16))) := by
  simp only [decrypt] at h
  split at h
  · simp at h
  · split at h
    · rename_i htag
      exact eq_of_beq htag
    · simp at h

end Aead.Spec
