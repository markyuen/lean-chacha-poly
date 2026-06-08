/-!
# ChaCha20 Stream Cipher — Specification

RFC 8439 §2.1–2.4. ChaCha20 is an ARX (add-rotate-XOR) stream
cipher. It generates a keystream by applying 20 rounds of
quarter-round mixing to a 512-bit state, then XORs that keystream
with the message.

## Why ChaCha20 is good for verification

- No field inversion, no modular exponentiation — only addition,
  rotation, and XOR of 32-bit words.
- The core correctness property (involution) is elegant: XOR is
  its own inverse, so encrypt = decrypt. The proof decomposes
  cleanly into keystream-length correctness and XOR cancellation.
- No external dependencies, no axioms.

## Module structure

  ChaCha20.Spec          ← this file: types, definitions, capstones
  ChaCha20.Spec.QuarterRound  ← quarter-round properties
  ChaCha20.Spec.Block         ← block function properties
  ChaCha20.Spec.Keystream     ← keystream generation properties
  ChaCha20.Spec.Xor           ← XOR cancellation lemmas
  ChaCha20.Native             ← ByteArray bridge + equivalence
-/
namespace ChaCha20.Spec

/-! ## Types -/

/-- A 256-bit (32-byte) ChaCha20 key. -/
structure Key where
  bytes : List UInt8
  size  : bytes.length = 32

/-- A 96-bit (12-byte) nonce. -/
structure Nonce where
  bytes : List UInt8
  size  : bytes.length = 12

/-- Build a `Key` from a byte list, returning `none` unless it is exactly
    32 bytes. -/
def Key.ofBytes? (bs : List UInt8) : Option Key :=
  if h : bs.length = 32 then some { bytes := bs, size := h } else none

/-- Build a `Nonce` from a byte list, returning `none` unless it is exactly
    12 bytes. -/
def Nonce.ofBytes? (bs : List UInt8) : Option Nonce :=
  if h : bs.length = 12 then some { bytes := bs, size := h } else none

/-- The ChaCha20 internal state: 16 × UInt32 words. -/
abbrev State := Array UInt32

/-! ## Constants -/

/-- "expand 32-byte k" as four little-endian UInt32 words. -/
def magic : Array UInt32 :=
  #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-! ## Little-endian serialization -/

def leToU32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8)
              ||| (b2.toUInt32 <<< 16)
              ||| (b3.toUInt32 <<< 24)

def u32ToLe (w : UInt32) : List UInt8 :=
  [ UInt8.ofNat (w.toNat % 256),
    UInt8.ofNat ((w.toNat >>> 8)  % 256),
    UInt8.ofNat ((w.toNat >>> 16) % 256),
    UInt8.ofNat ((w.toNat >>> 24) % 256) ]

/-! ## Quarter round (RFC 8439 §2.1) -/

/-- Left rotate a 32-bit word by n bits. -/
def rotl32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/-- The core ARX mixing step. -/
def quarterRound (a b c d : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := a + b; let d := rotl32 (d ^^^ a) 16
  let c := c + d; let b := rotl32 (b ^^^ c) 12
  let a := a + b; let d := rotl32 (d ^^^ a) 8
  let c := c + d; let b := rotl32 (b ^^^ c) 7
  (a, b, c, d)

/-- Apply a quarter round in-place to positions i,j,k,l of a State. -/
def qr (s : State) (i j k l : Fin 16) : State :=
  let (a, b, c, d) := quarterRound s[i.val]! s[j.val]! s[k.val]! s[l.val]!
  s.set! i.val a |>.set! j.val b |>.set! k.val c |>.set! l.val d

/-! ## Block function (RFC 8439 §2.3) -/

/-- Initialize the 16-word state from key, nonce, counter. -/
def initState (key : Key) (nonce : Nonce) (counter : UInt32) : State :=
  let k := key.bytes
  let n := nonce.bytes
  #[ magic[0]!, magic[1]!, magic[2]!, magic[3]!,
     leToU32 k[0]!  k[1]!  k[2]!  k[3]!,
     leToU32 k[4]!  k[5]!  k[6]!  k[7]!,
     leToU32 k[8]!  k[9]!  k[10]! k[11]!,
     leToU32 k[12]! k[13]! k[14]! k[15]!,
     leToU32 k[16]! k[17]! k[18]! k[19]!,
     leToU32 k[20]! k[21]! k[22]! k[23]!,
     leToU32 k[24]! k[25]! k[26]! k[27]!,
     leToU32 k[28]! k[29]! k[30]! k[31]!,
     counter,
     leToU32 n[0]! n[1]! n[2]!  n[3]!,
     leToU32 n[4]! n[5]! n[6]!  n[7]!,
     leToU32 n[8]! n[9]! n[10]! n[11]! ]

/-- One double-round (column round + diagonal round). -/
def doubleRound (s : State) : State :=
  -- Column rounds
  let s := qr s ⟨0,by omega⟩ ⟨4,by omega⟩ ⟨8,by omega⟩  ⟨12,by omega⟩
  let s := qr s ⟨1,by omega⟩ ⟨5,by omega⟩ ⟨9,by omega⟩  ⟨13,by omega⟩
  let s := qr s ⟨2,by omega⟩ ⟨6,by omega⟩ ⟨10,by omega⟩ ⟨14,by omega⟩
  let s := qr s ⟨3,by omega⟩ ⟨7,by omega⟩ ⟨11,by omega⟩ ⟨15,by omega⟩
  -- Diagonal rounds
  let s := qr s ⟨0,by omega⟩ ⟨5,by omega⟩ ⟨10,by omega⟩ ⟨15,by omega⟩
  let s := qr s ⟨1,by omega⟩ ⟨6,by omega⟩ ⟨11,by omega⟩ ⟨12,by omega⟩
  let s := qr s ⟨2,by omega⟩ ⟨7,by omega⟩ ⟨8,by omega⟩  ⟨13,by omega⟩
  qr s ⟨3,by omega⟩ ⟨4,by omega⟩ ⟨9,by omega⟩  ⟨14,by omega⟩

/-- Ten double-rounds. -/
def tenDoubleRounds (s : State) : State :=
  (List.replicate 10 ()).foldl (fun acc _ => doubleRound acc) s

/-- Add two states word-by-word. -/
def addStates (s t : State) : State :=
  Array.zipWith (· + ·) s t

/-- The full ChaCha20 block function:
    mix for 20 rounds, then add back the original state. -/
def chacha20Block (key : Key) (nonce : Nonce) (counter : UInt32) : State :=
  let s := initState key nonce counter
  addStates (tenDoubleRounds s) s

/-- Serialize a 16-word state to 64 bytes (little-endian). -/
def serializeBlock (s : State) : List UInt8 :=
  s.toList.flatMap u32ToLe

/-! ## Keystream and encryption (RFC 8439 §2.4) -/

/-- Generate `len` bytes of keystream. -/
def keystream (key : Key) (nonce : Nonce) (counter : UInt32) (len : Nat) : List UInt8 :=
  let nBlocks := (len + 63) / 64
  let stream := (List.range nBlocks).flatMap fun i =>
    serializeBlock (chacha20Block key nonce (counter + UInt32.ofNat i))
  stream.take len

/-- XOR two byte lists element-wise (truncates to shorter). -/
def xorBytes (a b : List UInt8) : List UInt8 :=
  List.zipWith (· ^^^ ·) a b

/-- Encrypt or decrypt a message. -/
def chacha20 (key : Key) (nonce : Nonce) (counter : UInt32)
    (msg : List UInt8) : List UInt8 :=
  xorBytes msg (keystream key nonce counter msg.length)


/-! ================================================================
    CAPSTONE THEOREMS
    ================================================================ -/

/-! ### C1: Involution

    Applying chacha20 twice with the same parameters returns the
    original message. This is the fundamental correctness guarantee:
    encrypt and decrypt are the same operation.

    Proof sketch:
      chacha20 k n ctr (chacha20 k n ctr msg)
      = xorBytes (xorBytes msg ks) ks     [unfold twice]
      = msg                                [xorBytes_self_cancel]
    where ks = keystream k n ctr msg.length, and the length
    argument is satisfied by keystream_length.

    `chacha20_involutive` (C1) and `chacha20_length` (C2) are proved in
    `ChaCha20.Spec.Keystream`: their proofs need `xorBytes_self_cancel`
    (Spec.Xor) and `keystream_length` (Spec.Keystream), which both import
    this file, so they cannot be discharged here without a cyclic import.
    They keep the `ChaCha20.Spec.*` qualified name regardless of file. -/

/-! ### C2: Length preservation — proved in Spec.Keystream -/

/-! ### C3: Keystream length — proved in Spec.Keystream -/

/-! ### C4: Block size — proved in Spec.Block -/

/-! ### C5: State size invariant -/
theorem initState_size (key : Key) (nonce : Nonce) (counter : UInt32) :
    (initState key nonce counter).size = 16 := by
  simp [initState]

theorem doubleRound_size (s : State) (h : s.size = 16) :
    (doubleRound s).size = 16 := by
  simp [doubleRound, qr]
  exact h

theorem tenDoubleRounds_size (s : State) (h : s.size = 16) :
    (tenDoubleRounds s).size = 16 := by
  simp [tenDoubleRounds]
  repeat rw [doubleRound_size]
  exact h

end ChaCha20.Spec
