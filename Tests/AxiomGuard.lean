import LeanChachaPoly

/-!
# Axiom guard

Compile-time enforcement that the capstones' axiom sets never silently grow:
each `#guard_msgs` below **fails the build** if `#print axioms` reports anything
other than the recorded set. Everything closes over Lean's three foundational
axioms (`propext`, `Classical.choice`, `Quot.sound`), with one documented
exception: `quarterRound_bijective` carries two `bv_decide` axioms, each stating
that the Lean-verified LRAT checker accepted one SAT certificate (the solver is
untrusted; the checker run is natively compiled rather than kernel-reduced, so
the compiler is trusted for exactly those two Boolean evaluations).

If a legitimate change alters an axiom set (e.g. removing the `bv_decide`
dependency), update the corresponding doc-comment here so the change appears
in review.
-/

/-! ## ChaCha20 -/

/-- info: 'ChaCha20.Spec.chacha20_involutive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ChaCha20.Spec.chacha20_involutive

/--
info: 'ChaCha20.Spec.quarterRound_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ChaCha20.Spec.quarterRoundInv_quarterRound._native.bv_decide.ax_1_10,
 ChaCha20.Spec.quarterRound_quarterRoundInv._native.bv_decide.ax_1_10]
-/
#guard_msgs in #print axioms ChaCha20.Spec.quarterRound_bijective

/-! ## Poly1305 -/

/-- info: 'Poly1305.Spec.poly1305_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.poly1305_value

/-- info: 'Poly1305.Spec.toBlocks_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.toBlocks_inj

/-- info: 'Poly1305.Spec.clampImage_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.clampImage_card

/-- info: 'Poly1305.Spec.clamp_fiber_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.clamp_fiber_card

/-- info: 'Poly1305.Spec.poly1305_almost_universal_msg'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.poly1305_almost_universal_msg'

/-- info: 'Poly1305.Spec.poly1305_byte_forgery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.poly1305_byte_forgery

/-- info: 'Poly1305.Spec.poly1305_clamped_forgery_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.poly1305_clamped_forgery_prob

/-- info: 'Poly1305.Spec.poly1305_tag_forgery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.poly1305_tag_forgery

/-- info: 'Poly1305.Spec.poly1305_tag_forgery_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.poly1305_tag_forgery_prob

/-- info: 'Poly1305.Spec.poly1305_adversary_forgery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.poly1305_adversary_forgery

/-- info: 'Poly1305.Spec.poly1305_adversary_forgery_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.poly1305_adversary_forgery_prob

/-- info: 'Poly1305.Spec.poly1305_adversary_forgery_multi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Spec.poly1305_adversary_forgery_multi

/--
info: 'Poly1305.Spec.poly1305_adversary_forgery_multi_prob' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Poly1305.Spec.poly1305_adversary_forgery_multi_prob

/-! ## AEAD -/

/-- info: 'Aead.Spec.decrypt_encrypt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aead.Spec.decrypt_encrypt

/-- info: 'Aead.Spec.decrypt_verifies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Aead.Spec.decrypt_verifies

/-- info: 'Aead.Spec.decryptCT_eq_decrypt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aead.Spec.decryptCT_eq_decrypt

/-- info: 'Aead.Spec.macData_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aead.Spec.macData_inj

/-- info: 'Aead.Spec.aead_forgery_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aead.Spec.aead_forgery_bound

/-- info: 'Aead.Spec.aead_forgery_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aead.Spec.aead_forgery_prob

/-! ## Fast implementation bridges

The fast `ByteArray` implementation equals the spec on every input. These
bridges use no `bv_decide` certificates and no native evaluation — only the
three foundational axioms. -/

/-- info: 'ChaCha20.Fast.chacha20_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ChaCha20.Fast.chacha20_eq_spec

/-- info: 'Poly1305.Fast.poly1305_eq_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Poly1305.Fast.poly1305_eq_spec

/-- info: 'Aead.Fast.encrypt_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aead.Fast.encrypt_eq_spec

/-- info: 'Aead.Fast.decrypt_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aead.Fast.decrypt_eq_spec

/-- info: 'Aead.Fast.decrypt_encrypt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aead.Fast.decrypt_encrypt
