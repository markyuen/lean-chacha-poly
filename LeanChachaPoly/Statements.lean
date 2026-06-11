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

open scoped Classical in
/-- **Poly1305 forgery probability (conditional).** Having observed the genuine tag
    `t` on `M`, a forger turns it into a tag `t'` on a different message `M' ≠ M`
    with probability at most `8·max ⌈|M|/16⌉ ⌈|M'|/16⌉ / 2¹⁰⁶`. The one-time pad makes
    the observation independent of the multiplier `r`, so conditioning does not help.
    The key is modelled as `(r, s)` over `keySpace`; `observed` is exactly the
    Poly1305 tag event (`observed_iff_poly1305`). -/
theorem poly1305_forgery_probability (M M' : List UInt8) (hne : M ≠ M')
    (t t' : Bytes 16) :
    ((Poly1305.Spec.keySpace.filter
        (fun rs => Poly1305.Spec.observed M t rs ∧ Poly1305.Spec.observed M' t' rs)).card : ℝ)
      / (Poly1305.Spec.keySpace.filter (Poly1305.Spec.observed M t)).card
      ≤ ((8 * max ((M.length + 15) / 16) ((M'.length + 15) / 16) : ℕ) : ℝ) / 2 ^ 106 :=
  Poly1305.Spec.poly1305_tag_forgery_cond_prob M M' hne t t'

open scoped Classical in
/-- **AEAD forgery probability.** With the one-time poly key uniform over the
    clamped values (the ChaCha20-PRF idealization — the one computational
    assumption), modifying `(aad, ciphertext)` yields an accepted forgery with
    probability at most `8·max ⌈L/16⌉ ⌈L'/16⌉ / 2¹⁰⁶` over the `macData` lengths. -/
theorem aead_forgery_probability (aad ct aad' ct' : List UInt8)
    (ha : aad.length < 2 ^ 64) (hc : ct.length < 2 ^ 64)
    (ha' : aad'.length < 2 ^ 64) (hc' : ct'.length < 2 ^ 64)
    (hne : (aad, ct) ≠ (aad', ct')) (t t' : Bytes 16) :
    ((Poly1305.Spec.clampedKeys.filter (fun r : ZMod Poly1305.Spec.P =>
        ∃ pkey : Poly1305.Spec.Key,
          ((Poly1305.Spec.extractR pkey : Nat) : ZMod Poly1305.Spec.P) = r ∧
          Poly1305.Spec.poly1305 pkey (Aead.Spec.macData aad ct).val = t ∧
          Poly1305.Spec.poly1305 pkey (Aead.Spec.macData aad' ct').val = t')).card : ℝ)
      / Poly1305.Spec.clampedKeys.card
      ≤ ((8 * max (((Aead.Spec.macData aad ct).val.length + 15) / 16)
                  (((Aead.Spec.macData aad' ct').val.length + 15) / 16) : ℕ) : ℝ) / 2 ^ 106 :=
  Aead.Spec.aead_forgery_prob aad ct aad' ct' ha hc ha' hc' hne t t'

/-- **The Poly1305 prime is prime.** `2¹³⁰ − 5` is prime (axiom-free Lucas/Pratt
    certificate), so the field-level bounds above are unconditional. -/
theorem poly1305_modulus_is_prime : Nat.Prime Poly1305.Spec.P :=
  Poly1305.Spec.prime_P

/-! ## The fast implementation equals the spec

    The `ByteArray` implementation that actually runs produces exactly the spec's
    bytes on every input, so every result above transfers to it. -/

/-- **ChaCha20: fast equals spec.** The `ByteArray` ChaCha20 produces exactly the
    spec's bytes on every input. -/
theorem fast_chacha20_eq_spec (key : ChaCha20.Fast.Key) (nonce : ChaCha20.Fast.Nonce)
    (counter : UInt32) (message : ByteArray) :
    (ChaCha20.Fast.chacha20 key nonce counter message).data.toList
      = ChaCha20.Spec.chacha20 key.toSpec nonce.toSpec counter message.data.toList :=
  ChaCha20.Fast.chacha20_eq_spec key nonce counter message

/-- **Poly1305: fast equals spec.** The `ByteArray` Poly1305 produces exactly the
    spec's 16-byte tag on every input. -/
theorem fast_poly1305_eq_spec (key : Poly1305.Fast.Key) (message : ByteArray) :
    (Poly1305.Fast.poly1305 key message).data.toList
      = (Poly1305.Spec.poly1305 key.toSpec message.data.toList).val :=
  Poly1305.Fast.poly1305_eq_spec key message

/-- **AEAD encryption: fast equals spec.** -/
theorem fast_encrypt_eq_spec (key : Aead.Fast.Key) (nonce : Aead.Fast.Nonce)
    (plaintext aad : ByteArray) :
    (Aead.Fast.encrypt key nonce plaintext aad).data.toList
      = Aead.Spec.encrypt key.toSpec nonce.toSpec plaintext.data.toList aad.data.toList :=
  Aead.Fast.encrypt_eq_spec key nonce plaintext aad

/-- **AEAD decryption: fast equals spec** — rejecting exactly the same forgeries, so
    every result above transfers to the code that runs. -/
theorem fast_decrypt_eq_spec (key : Aead.Fast.Key) (nonce : Aead.Fast.Nonce)
    (ciphertextAndTag aad : ByteArray) :
    (Aead.Fast.decrypt key nonce ciphertextAndTag aad).map (·.data.toList)
      = Aead.Spec.decrypt key.toSpec nonce.toSpec
          ciphertextAndTag.data.toList aad.data.toList :=
  Aead.Fast.decrypt_eq_spec key nonce ciphertextAndTag aad

end LeanChachaPoly.Statements
