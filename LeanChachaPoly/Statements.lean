import LeanChachaPoly.ChaCha20.Correctness
import LeanChachaPoly.Aead.Correctness
import LeanChachaPoly.Aead.Security
import LeanChachaPoly.Poly1305.Security
import LeanChachaPoly.Poly1305.Spec.Primality
import LeanChachaPoly.Fast.Bridge.ChaCha20
import LeanChachaPoly.Fast.Bridge.Poly1305
import LeanChachaPoly.Fast.Bridge.Aead

/-!
# Statements — the capstones in one place

A referee's reading list. Each headline result is restated here in the plainest
vocabulary available and proved as a one-line corollary of the capstone it names,
so the reader can see *what* is proved without chasing `Finset.filter` over
`ZMod P` through five files. Because every entry is a corollary, the build breaks
if a capstone's statement drifts — this file is self-maintaining, complementing
`Tests/AxiomGuard.lean` (which pins the *axioms*).

Nothing new is proved here; for the proofs follow each entry to its source.
-/

namespace LeanChachaPoly.Statements

/-! ## Functional correctness -/

/-- **ChaCha20 is its own inverse.** Encrypting a ciphertext with the same key,
    nonce and counter returns the plaintext — one routine both encrypts and
    decrypts. -/
theorem chacha20_decrypts_what_it_encrypts
    (key : ChaCha20.Spec.Key) (nonce : ChaCha20.Spec.Nonce) (counter : UInt32)
    (message : List UInt8) :
    ChaCha20.Spec.chacha20 key nonce counter
        (ChaCha20.Spec.chacha20 key nonce counter message) = message :=
  ChaCha20.Spec.chacha20_involutive key nonce counter message

/-- **AEAD round-trip.** Decrypting an encryption returns the original plaintext
    (and never `none`). -/
theorem aead_decrypt_of_encrypt
    (key : Aead.Spec.Key) (nonce : Aead.Spec.Nonce) (plaintext aad : List UInt8) :
    Aead.Spec.decrypt key nonce (Aead.Spec.encrypt key nonce plaintext aad) aad
      = some plaintext :=
  Aead.Spec.decrypt_encrypt key nonce plaintext aad

/-! ## Authenticity -/

/-- **Verify before release.** `decrypt` returns plaintext only when the received
    tag (the last 16 bytes) equals the Poly1305 tag recomputed over the derived
    one-time key and `macData aad ciphertext`: no path releases plaintext on an
    authentication failure. -/
theorem aead_authenticates_before_release
    (key : Aead.Spec.Key) (nonce : Aead.Spec.Nonce) (ctAndTag aad pt : List UInt8)
    (h : Aead.Spec.decrypt key nonce ctAndTag aad = some pt) :
    ctAndTag.drop (ctAndTag.length - 16)
      = (Poly1305.Spec.poly1305 (Aead.Spec.derivePolyKey key nonce)
          (Aead.Spec.macData aad (ctAndTag.take (ctAndTag.length - 16))).val).val :=
  Aead.Spec.decrypt_verifies key nonce ctAndTag aad pt h

/-- **Associated data is bound.** The length-framed MAC input is injective in
    `(aad, ciphertext)` (within the RFC's `2⁶⁴` length bounds): changing either
    changes the authenticated input. -/
theorem aead_binds_aad_and_ciphertext
    (aad₁ ct₁ aad₂ ct₂ : List UInt8)
    (ha1 : aad₁.length < 2 ^ 64) (hc1 : ct₁.length < 2 ^ 64)
    (ha2 : aad₂.length < 2 ^ 64) (hc2 : ct₂.length < 2 ^ 64)
    (h : Aead.Spec.macData aad₁ ct₁ = Aead.Spec.macData aad₂ ct₂) :
    aad₁ = aad₂ ∧ ct₁ = ct₂ :=
  Aead.Spec.macData_inj aad₁ ct₁ aad₂ ct₂ ha1 hc1 ha2 hc2 h

/-! ## Information-theoretic security

    Forgery probabilities, over the one-time key modelled as `(r, s)` — multiplier
    `r` uniform over the `2¹⁰⁶` clamped field values, pad `s ∈ [0, 2¹²⁸)`. -/

/-- **Poly1305 forgery probability (conditional).** Having observed the genuine tag
    `t` on `M`, a forger turns it into a tag `t'` on a different message `M' ≠ M`
    with probability at most `8·max ⌈|M|/16⌉ ⌈|M'|/16⌉ / 2¹⁰⁶`. The one-time pad makes
    the observation independent of the multiplier `r`, so conditioning does not help.
    (The key is modelled as `(r, s)` over `keySpace`; see `poly1305_tag_forgery_cond_prob`.) -/
alias poly1305_forgery_probability := Poly1305.Spec.poly1305_tag_forgery_cond_prob

/-- **AEAD forgery probability.** With the one-time poly key uniform over the
    clamped values (the ChaCha20-PRF idealization — the one computational
    assumption), modifying `(aad, ciphertext)` yields an accepted forgery with
    probability at most `8·max ⌈L/16⌉ ⌈L'/16⌉ / 2¹⁰⁶` over the `macData` lengths. -/
alias aead_forgery_probability := Aead.Spec.aead_forgery_prob

/-- **The Poly1305 prime is prime.** `2¹³⁰ − 5` is prime (axiom-free Lucas/Pratt
    certificate), so the field-level bounds above are unconditional. -/
theorem poly1305_modulus_is_prime : Nat.Prime Poly1305.Spec.P :=
  Poly1305.Spec.prime_P

/-! ## The fast implementation equals the spec

    The `ByteArray` implementation that actually runs produces exactly the spec's
    bytes on every input, so every result above transfers to it. -/

/-- ChaCha20: fast equals spec. -/
alias fast_chacha20_eq_spec := ChaCha20.Fast.chacha20_eq_spec
/-- Poly1305: fast equals spec. -/
alias fast_poly1305_eq_spec := Poly1305.Fast.poly1305_eq_spec
/-- AEAD encryption: fast equals spec. -/
alias fast_encrypt_eq_spec := Aead.Fast.encrypt_eq_spec
/-- AEAD decryption: fast equals spec (rejects exactly the same forgeries). -/
alias fast_decrypt_eq_spec := Aead.Fast.decrypt_eq_spec

end LeanChachaPoly.Statements
