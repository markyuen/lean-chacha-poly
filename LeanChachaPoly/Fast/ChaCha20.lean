import LeanChachaPoly.Fast.Types

/-!
# ChaCha20 — fast implementation

A compiled-speed ChaCha20 over `ByteArray`:

- The 512-bit state is a 16-field structure of `UInt32` (`St`) — one heap
  object of unboxed scalars; the rounds are fully unrolled over its fields.
- The round mixing reuses `ChaCha20.Spec.quarterRound` *verbatim* (inlined),
  so the fast and spec round functions contain literally the same ARX terms —
  the bridge proof never reasons about ARX semantics.
- Keystream bytes are pushed into a capacity-reserved `ByteArray`
  (`ByteArray.push` into reserved capacity is an in-place O(1) write), and
  XOR is a single indexed pass.

Equivalence with `ChaCha20.Spec.chacha20` is proved in
`LeanChachaPoly.Fast.Bridge.ChaCha20` (`chacha20_eq_spec`).

This file is Mathlib-free; it is linked into the `test` and `bench`
executables.
-/

namespace ChaCha20.Fast

open ChaCha20.Spec (quarterRound leToU32)

/-! ## State -/

/-- The ChaCha20 state as 16 named `UInt32` fields (unboxed scalars). -/
structure St where
  (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32)

/-- View an `St` as the spec's `State` (a literal 16-element array). -/
def St.toState (s : St) : ChaCha20.Spec.State :=
  ⟨#[s.x0, s.x1, s.x2, s.x3, s.x4, s.x5, s.x6, s.x7,
     s.x8, s.x9, s.x10, s.x11, s.x12, s.x13, s.x14, s.x15], rfl⟩

/-! ## Rounds -/

/-- One double-round (column round + diagonal round), fully unrolled.
    The quarter-round calls are the spec's `quarterRound`, in the spec's
    order. -/
def doubleRound (s : St) : St :=
  -- Column rounds
  let (x0, x4, x8,  x12) := quarterRound s.x0 s.x4 s.x8  s.x12
  let (x1, x5, x9,  x13) := quarterRound s.x1 s.x5 s.x9  s.x13
  let (x2, x6, x10, x14) := quarterRound s.x2 s.x6 s.x10 s.x14
  let (x3, x7, x11, x15) := quarterRound s.x3 s.x7 s.x11 s.x15
  -- Diagonal rounds
  let (x0, x5, x10, x15) := quarterRound x0 x5 x10 x15
  let (x1, x6, x11, x12) := quarterRound x1 x6 x11 x12
  let (x2, x7, x8,  x13) := quarterRound x2 x7 x8  x13
  let (x3, x4, x9,  x14) := quarterRound x3 x4 x9  x14
  ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩

/-- `n` double-rounds, tail-recursively. -/
def rounds : Nat → St → St
  | 0, s => s
  | n + 1, s => rounds n (doubleRound s)

/-- Add two states word-by-word. -/
def addSt (a b : St) : St :=
  ⟨a.x0 + b.x0, a.x1 + b.x1, a.x2 + b.x2, a.x3 + b.x3,
   a.x4 + b.x4, a.x5 + b.x5, a.x6 + b.x6, a.x7 + b.x7,
   a.x8 + b.x8, a.x9 + b.x9, a.x10 + b.x10, a.x11 + b.x11,
   a.x12 + b.x12, a.x13 + b.x13, a.x14 + b.x14, a.x15 + b.x15⟩

/-! ## Block function -/

/-- Initialize the state from key, nonce, counter (RFC 8439 §2.3). Same
    little-endian word loads as `Spec.initState`, with the bounds discharged
    by the `BytesA` size invariants. -/
def initSt (key : Key) (nonce : Nonce) (counter : UInt32) : St :=
  let k (i : Nat) (h : i < 32) : UInt8 := key.get i h
  let n (i : Nat) (h : i < 12) : UInt8 := nonce.get i h
  { x0  := 0x61707865, x1 := 0x3320646e, x2 := 0x79622d32, x3 := 0x6b206574
    x4  := leToU32 (k 0 (by omega))  (k 1 (by omega))  (k 2 (by omega))  (k 3 (by omega))
    x5  := leToU32 (k 4 (by omega))  (k 5 (by omega))  (k 6 (by omega))  (k 7 (by omega))
    x6  := leToU32 (k 8 (by omega))  (k 9 (by omega))  (k 10 (by omega)) (k 11 (by omega))
    x7  := leToU32 (k 12 (by omega)) (k 13 (by omega)) (k 14 (by omega)) (k 15 (by omega))
    x8  := leToU32 (k 16 (by omega)) (k 17 (by omega)) (k 18 (by omega)) (k 19 (by omega))
    x9  := leToU32 (k 20 (by omega)) (k 21 (by omega)) (k 22 (by omega)) (k 23 (by omega))
    x10 := leToU32 (k 24 (by omega)) (k 25 (by omega)) (k 26 (by omega)) (k 27 (by omega))
    x11 := leToU32 (k 28 (by omega)) (k 29 (by omega)) (k 30 (by omega)) (k 31 (by omega))
    x12 := counter
    x13 := leToU32 (n 0 (by omega))  (n 1 (by omega))  (n 2 (by omega))  (n 3 (by omega))
    x14 := leToU32 (n 4 (by omega))  (n 5 (by omega))  (n 6 (by omega))  (n 7 (by omega))
    x15 := leToU32 (n 8 (by omega))  (n 9 (by omega))  (n 10 (by omega)) (n 11 (by omega)) }

/-- The full ChaCha20 block function: 20 rounds of mixing, then add back the
    initial state. -/
def block (key : Key) (nonce : Nonce) (counter : UInt32) : St :=
  let s := initSt key nonce counter
  addSt (rounds 10 s) s

/-! ## Serialization -/

/-- Push a `UInt32` as 4 little-endian bytes. -/
@[inline] def pushU32le (acc : ByteArray) (w : UInt32) : ByteArray :=
  (((acc.push w.toUInt8).push (w >>> 8).toUInt8).push
    (w >>> 16).toUInt8).push (w >>> 24).toUInt8

/-- Push a state as 64 little-endian bytes. -/
def pushBlock (acc : ByteArray) (s : St) : ByteArray :=
  let acc := pushU32le acc s.x0
  let acc := pushU32le acc s.x1
  let acc := pushU32le acc s.x2
  let acc := pushU32le acc s.x3
  let acc := pushU32le acc s.x4
  let acc := pushU32le acc s.x5
  let acc := pushU32le acc s.x6
  let acc := pushU32le acc s.x7
  let acc := pushU32le acc s.x8
  let acc := pushU32le acc s.x9
  let acc := pushU32le acc s.x10
  let acc := pushU32le acc s.x11
  let acc := pushU32le acc s.x12
  let acc := pushU32le acc s.x13
  let acc := pushU32le acc s.x14
  pushU32le acc s.x15

/-! ## Keystream and encryption -/

/-- Generate the keystream blocks: `n` blocks starting at counter `ctr`,
    appended to `acc`. -/
def keystreamGo (key : Key) (nonce : Nonce) : Nat → UInt32 → ByteArray → ByteArray
  | 0, _, acc => acc
  | n + 1, ctr, acc => keystreamGo key nonce n (ctr + 1) (pushBlock acc (block key nonce ctr))

/-- Generate `len` bytes of keystream. Same counter-wrap caveat as
    `Spec.keystream`. -/
def keystream (key : Key) (nonce : Nonce) (counter : UInt32) (len : Nat) : ByteArray :=
  let nBlocks := (len + 63) / 64
  (keystreamGo key nonce nBlocks counter (ByteArray.emptyWithCapacity (nBlocks * 64))).extract 0 len

/-- XOR two byte arrays element-wise (truncates to shorter). -/
def xorBytes (a b : ByteArray) : ByteArray :=
  go 0 (ByteArray.emptyWithCapacity (min a.size b.size))
where
  go (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i < a.size ∧ i < b.size then
      go (i + 1) (acc.push ((a[i]'h.1) ^^^ (b[i]'h.2)))
    else acc
  termination_by min a.size b.size - i
  decreasing_by omega

/-- Encrypt or decrypt a message. -/
def chacha20 (key : Key) (nonce : Nonce) (counter : UInt32)
    (msg : ByteArray) : ByteArray :=
  xorBytes msg (keystream key nonce counter msg.size)

/-! ## Size facts (core-only, needed for subtype proofs downstream) -/

theorem size_pushU32le (acc : ByteArray) (w : UInt32) :
    (pushU32le acc w).size = acc.size + 4 := by
  simp [pushU32le]

theorem size_pushBlock (acc : ByteArray) (s : St) :
    (pushBlock acc s).size = acc.size + 64 := by
  simp [pushBlock, size_pushU32le]

theorem size_keystreamGo (key : Key) (nonce : Nonce) (n : Nat) (ctr : UInt32)
    (acc : ByteArray) :
    (keystreamGo key nonce n ctr acc).size = acc.size + n * 64 := by
  induction n generalizing ctr acc with
  | zero => simp [keystreamGo]
  | succ n ih => simp [keystreamGo, ih, size_pushBlock]; omega

theorem size_emptyWithCapacity (n : Nat) :
    (ByteArray.emptyWithCapacity n).size = 0 := rfl

/-- **Supporting.** The keystream has exactly the requested length. -/
theorem size_keystream (key : Key) (nonce : Nonce) (counter : UInt32) (len : Nat) :
    (keystream key nonce counter len).size = len := by
  simp only [keystream, ByteArray.size_extract, size_keystreamGo,
    size_emptyWithCapacity]
  omega

end ChaCha20.Fast
