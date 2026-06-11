import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.ChaCha20.Spec.Xor
import LeanChachaPoly.ChaCha20.Spec.Keystream
import LeanChachaPoly.Poly1305.Spec
import Std.Tactic.BVDecide

/-!
# ChaCha20-Poly1305 AEAD — Specification

RFC 8439 §2.8. Authenticated Encryption with Associated Data
constructed from ChaCha20 (encryption) and Poly1305 (authentication).

## The capstone theorem

  decrypt(encrypt(pt, aad)) = some pt

This is what the entire library exists to prove. The proof
decomposes into three sub-steps:

  1. `encrypt` appends `ct ‖ tag` where `ct = chacha20(1, pt)`
  2. `decrypt` recomputes the tag and finds it matches
     (by `poly1305` determinism — a pure function applied to
     the same inputs produces the same output)
  3. `decrypt` then returns `chacha20(1, ct) = chacha20(1, chacha20(1, pt)) = pt`
     by the ChaCha20 involution theorem

The entire proof is algebraic assembly — no new mathematical
content beyond what was proved in ChaCha20.Spec and Poly1305.Spec.

## Module structure

  Aead.Spec               ← this file: construction (encrypt/decrypt) only
  Aead.Correctness        ← roundtrip + length/shape capstones
  Aead.Security           ← authenticity: verify-before-decrypt, macData injectivity
  Aead.Spec.KeyDerivation ← derivePolyKey, padTo16/le64 lemmas
  Aead.Spec.MacData       ← macData injectivity lemmas
-/
namespace Aead.Spec

open ChaCha20.Spec Poly1305.Spec

/-! ## Types -/

abbrev Key   := ChaCha20.Spec.Key
abbrev Nonce := ChaCha20.Spec.Nonce

/-! ## Poly1305 one-time key derivation (RFC 8439 §2.6) -/

/-- Run ChaCha20 with counter=0, take first 32 bytes as the
    Poly1305 key. The 32-byte length is guaranteed by
    `keystream_length`. -/
def derivePolyKey (key : Key) (nonce : Nonce) : Poly1305.Spec.Key :=
  let stream := keystream key nonce 0 64
  ⟨stream.take 32, by rw [List.length_take, keystream_length]; decide⟩

/-! ## MAC data construction (RFC 8439 §2.8) -/

/-- Pad a byte list to a multiple of 16 with zeros. The 16-alignment is enforced
    by the `Padded` return type. -/
def padTo16 (data : List UInt8) : Padded :=
  if h : data.length % 16 = 0 then ⟨data, h⟩
  else ⟨data ++ List.replicate (16 - data.length % 16) 0, by
    rw [List.length_append, List.length_replicate]; omega⟩

/-- Encode a Nat as 8 bytes, little-endian. -/
def le64 (n : Nat) : Bytes 8 :=
  ⟨(List.range 8).map fun i => UInt8.ofNat ((n >>> (i * 8)) % 256), by simp⟩

/-- Construct the Poly1305 authentication input per RFC 8439 §2.8.
    Layout: pad(aad) ‖ pad(ciphertext) ‖ len(aad) as 8-LE ‖ len(ct) as 8-LE.
    The total length is a multiple of 16 (`Padded`). -/
def macData (aad ciphertext : List UInt8) : Padded :=
  ⟨(padTo16 aad).val ++ (padTo16 ciphertext).val ++
   (le64 aad.length).val ++ (le64 ciphertext.length).val, by
    have h1 := (padTo16 aad).property
    have h2 := (padTo16 ciphertext).property
    have h3 := (le64 aad.length).property
    have h4 := (le64 ciphertext.length).property
    simp only [List.length_append]
    omega⟩

/-! ## Constant-time-shaped tag comparison -/

/-- XOR of two bytes is zero exactly on equal bytes. -/
private theorem UInt8.xor_eq_zero (x y : UInt8) : x ^^^ y = 0 ↔ x = y := by bv_decide

/-- OR of two bytes is zero exactly when both are zero. -/
private theorem UInt8.or_eq_zero (x y : UInt8) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by bv_decide

/-- OR-accumulating a byte list onto `acc` is zero exactly when `acc` and every
    element are zero. -/
private theorem foldl_or_eq_zero : ∀ (l : List UInt8) (acc : UInt8),
    l.foldl (· ||| ·) acc = 0 ↔ acc = 0 ∧ ∀ x ∈ l, x = 0
  | [], acc => by simp
  | h :: t, acc => by
    rw [List.foldl_cons, foldl_or_eq_zero t, UInt8.or_eq_zero, List.forall_mem_cons]
    exact and_assoc

/-- Tag comparison that inspects every byte: equal lengths and a zero
    OR-accumulation of the per-byte XOR differences. No branch depends on which
    byte first differs, in place of the short-circuiting `==`. `ctEq_iff` proves
    it equals `=`, so substituting it leaves `decrypt` semantically unchanged. -/
def ctEq (a b : List UInt8) : Bool :=
  (a.length == b.length) && ((List.zipWith (· ^^^ ·) a b).foldl (· ||| ·) 0 == 0)

/-- **Key lemma.** `ctEq` decides list equality: `true` exactly when the byte lists
    are equal. The whole-tag scan returns the same verdict as `==`. -/
theorem ctEq_iff (a b : List UInt8) : ctEq a b = true ↔ a = b := by
  rw [ctEq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, foldl_or_eq_zero]
  constructor
  · rintro ⟨hlen, -, hz⟩
    apply List.ext_getElem hlen
    intro i h1 h2
    have hmem : (List.zipWith (· ^^^ ·) a b)[i]'(by rw [List.length_zipWith]; omega)
        ∈ List.zipWith (· ^^^ ·) a b := List.getElem_mem _
    rw [List.getElem_zipWith] at hmem
    exact (UInt8.xor_eq_zero _ _).mp (hz _ hmem)
  · rintro rfl
    refine ⟨rfl, rfl, fun x hx => ?_⟩
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rw [List.getElem_zipWith]
    exact (UInt8.xor_eq_zero _ _).mpr rfl

/-- `ctEq a a` is `true`. -/
@[simp] theorem ctEq_self (a : List UInt8) : ctEq a a = true := (ctEq_iff a a).mpr rfl

/-- `ctEq` agrees with `==`; the fast bridge rewrites the `ByteArray` comparison
    along this once both sides are reduced to lists. -/
theorem beq_eq_ctEq (a b : List UInt8) : (a == b) = ctEq a b := by
  by_cases h : a = b
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h]
    symm
    simp only [Bool.eq_false_iff, ne_eq, ctEq_iff]
    exact h

/-! ## Encrypt and decrypt -/

/-- AEAD encryption: returns ciphertext ‖ 16-byte tag. -/
def encrypt (key : Key) (nonce : Nonce)
    (plaintext aad : List UInt8) : List UInt8 :=
  let polyKey    := derivePolyKey key nonce
  let ciphertext := chacha20 key nonce 1 plaintext
  let tag        := poly1305 polyKey (macData aad ciphertext).val
  ciphertext ++ tag.val

/-- AEAD decryption: returns `some plaintext` on success,
    `none` if the tag does not match.

    **Timing caveat.** `recvTag == expTag.val` is a short-circuiting list
    comparison — the classic MAC timing leak if executed as-is. The functional
    spec only fixes input→output behavior; a production implementation must
    compare tags in constant time. `decryptCT` below is the same function with the
    short-circuit removed (`decryptCT_eq_decrypt`), and `ctEq_iff` certifies the
    replacement comparison still decides equality. -/
def decrypt (key : Key) (nonce : Nonce)
    (ciphertextAndTag aad : List UInt8) : Option (List UInt8) :=
  if ciphertextAndTag.length < 16 then none
  else
    let ctLen      := ciphertextAndTag.length - 16
    let ciphertext := ciphertextAndTag.take ctLen
    let recvTag    := ciphertextAndTag.drop ctLen
    let polyKey    := derivePolyKey key nonce
    let expTag     := poly1305 polyKey (macData aad ciphertext).val
    if recvTag == expTag.val then
      some (chacha20 key nonce 1 ciphertext)
    else none

/-- Constant-time-shaped decryption: identical to `decrypt` except the tag check
    uses `ctEq` (a whole-tag scan) in place of the short-circuiting `==`. The
    `decryptCT_eq_decrypt` theorem proves the two compute the same function, so
    every property proved of `decrypt` transfers; this variant only removes the
    first-mismatch branch at the source level. A runtime constant-time guarantee
    additionally requires the compiled comparison primitive to be branch-free,
    which is a property of the artifact, not of this spec. -/
def decryptCT (key : Key) (nonce : Nonce)
    (ciphertextAndTag aad : List UInt8) : Option (List UInt8) :=
  if ciphertextAndTag.length < 16 then none
  else
    let ctLen      := ciphertextAndTag.length - 16
    let ciphertext := ciphertextAndTag.take ctLen
    let recvTag    := ciphertextAndTag.drop ctLen
    let polyKey    := derivePolyKey key nonce
    let expTag     := poly1305 polyKey (macData aad ciphertext).val
    if ctEq recvTag expTag.val then
      some (chacha20 key nonce 1 ciphertext)
    else none

/-- **Key lemma.** The constant-time variant computes the same function as
    `decrypt`: the only difference is `==` versus `ctEq`, equal by `beq_eq_ctEq`. -/
theorem decryptCT_eq_decrypt : decryptCT = decrypt := by
  funext key nonce ciphertextAndTag aad
  simp only [decryptCT, decrypt, beq_eq_ctEq]

/-!
This file is construction only. The properties live elsewhere:
- functional roundtrip / length facts — `Aead.Correctness` (`decrypt_encrypt`, …)
- authenticity — `Aead/Security.lean` (`decrypt_verifies`, `macData_inj`, `aead_forgery_bound`)
- `macData`/`padTo16`/`le64` structural lemmas — `Aead/Spec/{KeyDerivation,MacData}.lean`
-/

end Aead.Spec
