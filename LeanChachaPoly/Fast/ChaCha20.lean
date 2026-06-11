import LeanChachaPoly.Fast.Types

/-!
# ChaCha20 — fast implementation

A compiled-speed ChaCha20 over `ByteArray`:

- The 512-bit state is a 16-field structure of `UInt32` (`St`) — one heap
  object of unboxed scalars; the rounds are fully unrolled over its fields.
- The round mixing reuses `ChaCha20.Spec.quarterRound` *verbatim* (inlined),
  so the fast and spec round functions contain literally the same ARX terms —
  the bridge proof never reasons about ARX semantics.
- Encryption is a fused single pass: each 64-byte block is computed with the
  16 state words register-threaded (`roundsGo` — the words are loop
  parameters, so the compiled loop keeps them in registers) and XOR-written
  in place into a pre-sized output with `ByteArray.set` (a static-inline
  store in the runtime, unlike the exported `ByteArray.push` call) — no
  intermediate keystream buffer. The push-based pass (`chacha20Push`) and
  the two-pass composition (`xorBytes` + `keystream`, needed by
  `derivePolyKey`) are retained as differential baselines.

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

/-- `n` double-rounds with the 16 state words register-threaded: the words are
    parameters, so the compiled loop keeps them in 16 `uint32` locals across
    all `n` iterations and allocates a single `St` at the end. Equals `rounds`
    (`roundsGo_eq` in the bridge). -/
def roundsGo : Nat →
    UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 →
    UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → St
  | 0, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15 =>
    ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩
  | n + 1, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15 =>
    -- Column rounds
    let (x0, x4, x8,  x12) := quarterRound x0 x4 x8  x12
    let (x1, x5, x9,  x13) := quarterRound x1 x5 x9  x13
    let (x2, x6, x10, x14) := quarterRound x2 x6 x10 x14
    let (x3, x7, x11, x15) := quarterRound x3 x7 x11 x15
    -- Diagonal rounds
    let (x0, x5, x10, x15) := quarterRound x0 x5 x10 x15
    let (x1, x6, x11, x12) := quarterRound x1 x6 x11 x12
    let (x2, x7, x8,  x13) := quarterRound x2 x7 x8  x13
    let (x3, x4, x9,  x14) := quarterRound x3 x4 x9  x14
    roundsGo n x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

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
    initial state. Fully fused: the 16 initial words are computed into locals
    (the same little-endian loads as `initSt`), mixed register-threaded
    (`roundsGo`), and added back inline — one `St` allocation per block.
    Equals `addSt (rounds 10 (initSt …)) (initSt …)`
    (`block_eq_addSt_rounds` in the bridge). -/
def block (key : Key) (nonce : Nonce) (counter : UInt32) : St :=
  let k (i : Nat) (h : i < 32) : UInt8 := key.get i h
  let n (i : Nat) (h : i < 12) : UInt8 := nonce.get i h
  let y0  : UInt32 := 0x61707865
  let y1  : UInt32 := 0x3320646e
  let y2  : UInt32 := 0x79622d32
  let y3  : UInt32 := 0x6b206574
  let y4  := leToU32 (k 0 (by omega))  (k 1 (by omega))  (k 2 (by omega))  (k 3 (by omega))
  let y5  := leToU32 (k 4 (by omega))  (k 5 (by omega))  (k 6 (by omega))  (k 7 (by omega))
  let y6  := leToU32 (k 8 (by omega))  (k 9 (by omega))  (k 10 (by omega)) (k 11 (by omega))
  let y7  := leToU32 (k 12 (by omega)) (k 13 (by omega)) (k 14 (by omega)) (k 15 (by omega))
  let y8  := leToU32 (k 16 (by omega)) (k 17 (by omega)) (k 18 (by omega)) (k 19 (by omega))
  let y9  := leToU32 (k 20 (by omega)) (k 21 (by omega)) (k 22 (by omega)) (k 23 (by omega))
  let y10 := leToU32 (k 24 (by omega)) (k 25 (by omega)) (k 26 (by omega)) (k 27 (by omega))
  let y11 := leToU32 (k 28 (by omega)) (k 29 (by omega)) (k 30 (by omega)) (k 31 (by omega))
  let y12 := counter
  let y13 := leToU32 (n 0 (by omega))  (n 1 (by omega))  (n 2 (by omega))  (n 3 (by omega))
  let y14 := leToU32 (n 4 (by omega))  (n 5 (by omega))  (n 6 (by omega))  (n 7 (by omega))
  let y15 := leToU32 (n 8 (by omega))  (n 9 (by omega))  (n 10 (by omega)) (n 11 (by omega))
  match roundsGo 10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 with
  | ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩ =>
    ⟨z0 + y0, z1 + y1, z2 + y2, z3 + y3, z4 + y4, z5 + y5, z6 + y6, z7 + y7,
     z8 + y8, z9 + y9, z10 + y10, z11 + y11, z12 + y12, z13 + y13, z14 + y14, z15 + y15⟩

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

/-! ## Fused keystream-XOR pass (push-based, retained)

Computes each 64-byte block in registers and XORs it directly against the
message bytes, pushing the output once — no intermediate keystream buffer.
Superseded by the in-place set-based pass below (`chacha20`); retained as
`chacha20Push` with the engines-agree corollary `chacha20_eq_pushPass`. The
two-pass composition (`xorBytes` of a materialized `keystream`) is retained
above; `chacha20_eq_twoPass` proves those engines agree. -/

/-- Push 4 message bytes XORed with the little-endian bytes of `w`. -/
@[inline] def pushXor4 (acc : ByteArray) (w : UInt32) (m : ByteArray) (i : Nat)
    (h : i + 4 ≤ m.size) : ByteArray :=
  (((acc.push ((m[i]'(by omega)) ^^^ w.toUInt8)).push
    ((m[i + 1]'(by omega)) ^^^ (w >>> 8).toUInt8)).push
    ((m[i + 2]'(by omega)) ^^^ (w >>> 16).toUInt8)).push
    ((m[i + 3]'(by omega)) ^^^ (w >>> 24).toUInt8)

/-- Push 64 message bytes at `off` XORed with the serialized state `s`. -/
def pushBlockXor (acc : ByteArray) (s : St) (m : ByteArray) (off : Nat)
    (h : off + 64 ≤ m.size) : ByteArray :=
  let acc := pushXor4 acc s.x0  m off        (by omega)
  let acc := pushXor4 acc s.x1  m (off + 4)  (by omega)
  let acc := pushXor4 acc s.x2  m (off + 8)  (by omega)
  let acc := pushXor4 acc s.x3  m (off + 12) (by omega)
  let acc := pushXor4 acc s.x4  m (off + 16) (by omega)
  let acc := pushXor4 acc s.x5  m (off + 20) (by omega)
  let acc := pushXor4 acc s.x6  m (off + 24) (by omega)
  let acc := pushXor4 acc s.x7  m (off + 28) (by omega)
  let acc := pushXor4 acc s.x8  m (off + 32) (by omega)
  let acc := pushXor4 acc s.x9  m (off + 36) (by omega)
  let acc := pushXor4 acc s.x10 m (off + 40) (by omega)
  let acc := pushXor4 acc s.x11 m (off + 44) (by omega)
  let acc := pushXor4 acc s.x12 m (off + 48) (by omega)
  let acc := pushXor4 acc s.x13 m (off + 52) (by omega)
  let acc := pushXor4 acc s.x14 m (off + 56) (by omega)
  pushXor4 acc s.x15 m (off + 60) (by omega)

/-- XOR the message tail `[off, m.size)` against the keystream bytes `ks`
    (truncating to the shorter), appended to `acc`. -/
def tailXor (acc : ByteArray) (m : ByteArray) (off : Nat) (ks : ByteArray) :
    ByteArray :=
  go 0 acc
where
  go (j : Nat) (acc : ByteArray) : ByteArray :=
    if h : off + j < m.size ∧ j < ks.size then
      go (j + 1) (acc.push ((m[off + j]'h.1) ^^^ (ks[j]'h.2)))
    else acc
  termination_by m.size - (off + j)
  decreasing_by omega

/-- The fused encryption loop: full 64-byte blocks are XORed in place via
    `pushBlockXor`; a trailing partial block serializes one scratch block and
    XORs the tail. -/
def chacha20Go (key : Key) (nonce : Nonce) (m : ByteArray) (ctr : UInt32)
    (off : Nat) (acc : ByteArray) : ByteArray :=
  if h : off + 64 ≤ m.size then
    chacha20Go key nonce m (ctr + 1) (off + 64)
      (pushBlockXor acc (block key nonce ctr) m off h)
  else if off < m.size then
    tailXor acc m off (pushBlock (ByteArray.emptyWithCapacity 64) (block key nonce ctr))
  else acc
  termination_by m.size - off
  decreasing_by omega

/-- The retained push-based fused pass (the previous `chacha20` body);
    `chacha20_eq_pushPass` proves the engines agree. -/
def chacha20Push (key : Key) (nonce : Nonce) (counter : UInt32)
    (msg : ByteArray) : ByteArray :=
  chacha20Go key nonce msg counter 0 (ByteArray.emptyWithCapacity msg.size)

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

/-! ## In-place fused pass (set-based)

The output is pre-sized with one `copySlice` (a memcpy of the message), then
each 64-byte block is XOR-written in place with `ByteArray.set` — which is a
static-inline store in the runtime, unlike the exported `ByteArray.push` call.
The push-based pass (`chacha20Go`/`chacha20Push`) is retained above;
`chacha20_eq_pushPass` proves the engines agree. -/

theorem size_set (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) :
    (a.set i v h).size = a.size := by
  rw [← ByteArray.size_data, ByteArray.data_set, Array.size_set, ByteArray.size_data]

/-- A `ByteArray` of known size `n` (output buffer carrying its size invariant). -/
abbrev SizedBA (n : Nat) := { o : ByteArray // o.size = n }

/-- XOR-write 4 bytes in place: `out[i+k] := m[i+k] ^^^ (w >>> 8k)`. -/
@[inline] def setXor4 (n : Nat) (out : SizedBA n) (w : UInt32) (m : ByteArray)
    (i : Nat) (hm : i + 4 ≤ m.size) (ho : i + 4 ≤ n) : SizedBA n :=
  have hsz := out.property
  ⟨((((out.val.set i ((m[i]'(by omega)) ^^^ w.toUInt8) (by omega)).set
      (i+1) ((m[i+1]'(by omega)) ^^^ (w >>> 8).toUInt8) (by simp [size_set]; omega)).set
      (i+2) ((m[i+2]'(by omega)) ^^^ (w >>> 16).toUInt8) (by simp [size_set]; omega)).set
      (i+3) ((m[i+3]'(by omega)) ^^^ (w >>> 24).toUInt8) (by simp [size_set]; omega)),
   by simp [size_set, hsz]⟩

/-- Bound glue for the unrolled writer at flat offsets (cheap term proofs;
    32 `omega` calls in one declaration would exhaust the heartbeat budget). -/
theorem le_of_off64 {off c bound : Nat} (hc : c + 4 ≤ 64)
    (h : off + 64 ≤ bound) : off + c + 4 ≤ bound := by omega

theorem le_of_off64' {off bound : Nat} (h : off + 64 ≤ bound) :
    off + 4 ≤ bound := by omega

/-- XOR-write 64 bytes at `off`: the message slice XOR the serialized state. -/
def setBlockXor (n : Nat) (out : SizedBA n) (s : St) (m : ByteArray) (off : Nat)
    (hm : off + 64 ≤ m.size) (ho : off + 64 ≤ n) : SizedBA n :=
  let o1  := setXor4 n out s.x0  m off        (le_of_off64' hm) (le_of_off64' ho)
  let o2  := setXor4 n o1  s.x1  m (off + 4)  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o3  := setXor4 n o2  s.x2  m (off + 8)  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o4  := setXor4 n o3  s.x3  m (off + 12) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o5  := setXor4 n o4  s.x4  m (off + 16) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o6  := setXor4 n o5  s.x5  m (off + 20) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o7  := setXor4 n o6  s.x6  m (off + 24) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o8  := setXor4 n o7  s.x7  m (off + 28) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o9  := setXor4 n o8  s.x8  m (off + 32) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o10 := setXor4 n o9  s.x9  m (off + 36) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o11 := setXor4 n o10 s.x10 m (off + 40) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o12 := setXor4 n o11 s.x11 m (off + 44) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o13 := setXor4 n o12 s.x12 m (off + 48) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o14 := setXor4 n o13 s.x13 m (off + 52) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  let o15 := setXor4 n o14 s.x14 m (off + 56) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  setXor4 n o15 s.x15 m (off + 60) (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)

/-- In-place tail XOR: `out[off+j] := m[off+j] ^^^ ks[j]` until either runs out. -/
def tailXorSet (m : ByteArray) (off : Nat) (ks : ByteArray) (j : Nat)
    (out : SizedBA m.size) : SizedBA m.size :=
  if h : off + j < m.size ∧ j < ks.size then
    tailXorSet m off ks (j + 1)
      ⟨out.val.set (off + j) ((m[off + j]'h.1) ^^^ (ks[j]'h.2))
         (by have := out.property; omega),
       by rw [size_set]; exact out.property⟩
  else out
  termination_by m.size - (off + j)
  decreasing_by omega

/-- The set-based fused encryption loop. -/
def chacha20SetGo (key : Key) (nonce : Nonce) (m : ByteArray) (ctr : UInt32)
    (off : Nat) (out : SizedBA m.size) : ByteArray :=
  if h : off + 64 ≤ m.size then
    chacha20SetGo key nonce m (ctr + 1) (off + 64)
      (setBlockXor m.size out (block key nonce ctr) m off h h)
  else if off < m.size then
    (tailXorSet m off
      (pushBlock (ByteArray.emptyWithCapacity 64) (block key nonce ctr)) 0 out).val
  else out.val
  termination_by m.size - off
  decreasing_by omega

/-! ## In-place fused pass (USize-indexed)

The same in-place writer as the set-based pass, but indexing the message and
output with `ByteArray.uget`/`uset` (raw `USize` indices → the static-inline
`lean_byte_array_uget`/`uset` in the runtime) instead of `getElem`/`set`
(boxed `Nat` indices). Sound only when every index fits a `USize`, i.e.
`m.size < USize.size`; `chacha20` takes that as a one-per-call runtime guard
and falls back to `chacha20Push` when it fails (never on a `ByteArray` that
the runtime can allocate — its length is stored as a `size_t`).
`chacha20SetGoU_eq` (bridge) proves this engine equals `chacha20SetGo` under
the guard, so it inherits `chacha20_eq_spec`. -/

/-- `(k : Nat).toUSize` round-trips through `toNat` when `k < USize.size`. -/
theorem toNat_toUSize_of_lt {k : Nat} (h : k < USize.size) : k.toUSize.toNat = k :=
  USize.toNat_ofNat_of_lt' h

/-- `ByteArray.uget` reads the same byte as `getElem` at the index's `Nat` value. -/
theorem uget_eq_getElem {a : ByteArray} {i : USize} {h : i.toNat < a.size} :
    a.uget i h = a[i.toNat]'h := by
  rcases a with ⟨bs⟩
  show bs[i] = _
  rw [Array.ugetElem_eq_getElem, ByteArray.getElem_eq_getElem_data]

/-- `ByteArray.uset` writes the same as `set` at the index's `Nat` value. -/
theorem uset_eq_set {a : ByteArray} {i : USize} {v : UInt8} {h : i.toNat < a.size} :
    a.uset i v h = a.set i.toNat v h := by
  rcases a with ⟨bs⟩
  show (⟨bs.uset i v h⟩ : ByteArray) = (⟨bs.set i.toNat v h⟩ : ByteArray)
  rw [Array.uset_eq_set]

theorem size_uset (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) :
    (a.uset i v h).size = a.size := by
  rw [uset_eq_set]; exact size_set a i.toNat v h

/-- The `USize` index `iU + c` reads back as the `Nat` index `i + c`, given the
    base relation `iU.toNat = i` and that `i + c` fits a `USize`. The index
    arithmetic stays in `USize` (no per-access `Nat → USize` conversion). -/
theorem uidx_eq {i c : Nat} {iU : USize} (hiU : iU.toNat = i) (hb : i + c < USize.size) :
    (iU + USize.ofNat c).toNat = i + c := by
  rw [USize.toNat_add, hiU, USize.toNat_ofNat_of_lt' (show c < USize.size by omega),
    Nat.mod_eq_of_lt hb]

/-- XOR-write 4 bytes in place via `uset` at the `USize` base `iU` (= `i`):
    `out[i+k] := m[i+k] ^^^ (w >>> 8k)`. The four byte indices are `USize`
    additions `iU + 0..3` — one `Nat → USize` conversion is amortized per block
    by the caller, not paid per byte. -/
@[inline] def setXor4U (n : Nat) (out : SizedBA n) (w : UInt32) (m : ByteArray)
    (i : Nat) (iU : USize) (hiU : iU.toNat = i)
    (hm : i + 4 ≤ m.size) (ho : i + 4 ≤ n) (hMN : m.size < USize.size) : SizedBA n :=
  have hsz := out.property
  ⟨((((out.val.uset (iU + USize.ofNat 0)
        ((m.uget (iU + USize.ofNat 0) (by rw [uidx_eq hiU (by omega)]; omega)) ^^^ w.toUInt8)
        (by rw [uidx_eq hiU (by omega)]; omega)).uset
      (iU + USize.ofNat 1)
        ((m.uget (iU + USize.ofNat 1) (by rw [uidx_eq hiU (by omega)]; omega)) ^^^ (w >>> 8).toUInt8)
        (by rw [uidx_eq hiU (by omega)]; simp only [size_uset]; omega)).uset
      (iU + USize.ofNat 2)
        ((m.uget (iU + USize.ofNat 2) (by rw [uidx_eq hiU (by omega)]; omega)) ^^^ (w >>> 16).toUInt8)
        (by rw [uidx_eq hiU (by omega)]; simp only [size_uset]; omega)).uset
      (iU + USize.ofNat 3)
        ((m.uget (iU + USize.ofNat 3) (by rw [uidx_eq hiU (by omega)]; omega)) ^^^ (w >>> 24).toUInt8)
        (by rw [uidx_eq hiU (by omega)]; simp only [size_uset]; omega)),
   by simp only [size_uset]; exact hsz⟩

/-- XOR-write 64 bytes at `off` via `uset` (the `setBlockXor` analogue). The
    `USize` base `offU` (= `off`) is computed once; each word's base is the
    `USize` addition `offU + 4k`. -/
def setBlockXorU (n : Nat) (out : SizedBA n) (s : St) (m : ByteArray) (off : Nat)
    (hm : off + 64 ≤ m.size) (ho : off + 64 ≤ n) (hMN : m.size < USize.size) : SizedBA n :=
  let offU := off.toUSize
  have hoffU : offU.toNat = off := toNat_toUSize_of_lt (by omega)
  let o1  := setXor4U n out s.x0  m off        offU                 hoffU                     (le_of_off64' hm) (le_of_off64' ho) hMN
  let o2  := setXor4U n o1  s.x1  m (off + 4)  (offU + USize.ofNat 4)  (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o3  := setXor4U n o2  s.x2  m (off + 8)  (offU + USize.ofNat 8)  (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o4  := setXor4U n o3  s.x3  m (off + 12) (offU + USize.ofNat 12) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o5  := setXor4U n o4  s.x4  m (off + 16) (offU + USize.ofNat 16) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o6  := setXor4U n o5  s.x5  m (off + 20) (offU + USize.ofNat 20) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o7  := setXor4U n o6  s.x6  m (off + 24) (offU + USize.ofNat 24) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o8  := setXor4U n o7  s.x7  m (off + 28) (offU + USize.ofNat 28) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o9  := setXor4U n o8  s.x8  m (off + 32) (offU + USize.ofNat 32) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o10 := setXor4U n o9  s.x9  m (off + 36) (offU + USize.ofNat 36) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o11 := setXor4U n o10 s.x10 m (off + 40) (offU + USize.ofNat 40) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o12 := setXor4U n o11 s.x11 m (off + 44) (offU + USize.ofNat 44) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o13 := setXor4U n o12 s.x12 m (off + 48) (offU + USize.ofNat 48) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o14 := setXor4U n o13 s.x13 m (off + 52) (offU + USize.ofNat 52) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  let o15 := setXor4U n o14 s.x14 m (off + 56) (offU + USize.ofNat 56) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN
  setXor4U n o15 s.x15 m (off + 60) (offU + USize.ofNat 60) (uidx_eq hoffU (by omega))  (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho) hMN

/-- In-place tail XOR via `uset` (the `tailXorSet` analogue). -/
def tailXorSetU (m : ByteArray) (off : Nat) (ks : ByteArray) (j : Nat)
    (out : SizedBA m.size) (hMN : m.size < USize.size) : SizedBA m.size :=
  if h : off + j < m.size ∧ j < ks.size then
    tailXorSetU m off ks (j + 1)
      ⟨out.val.uset (off + j).toUSize
         ((m.uget (off + j).toUSize (by rw [toNat_toUSize_of_lt (by omega)]; exact h.1)) ^^^ (ks[j]'h.2))
         (by rw [toNat_toUSize_of_lt (by omega)]; have := out.property; omega),
       by rw [size_uset]; exact out.property⟩ hMN
  else out
  termination_by m.size - (off + j)
  decreasing_by omega

/-- The USize-indexed set-based fused loop (the `chacha20SetGo` analogue). -/
def chacha20SetGoU (key : Key) (nonce : Nonce) (m : ByteArray) (ctr : UInt32)
    (off : Nat) (out : SizedBA m.size) (hMN : m.size < USize.size) : ByteArray :=
  if h : off + 64 ≤ m.size then
    chacha20SetGoU key nonce m (ctr + 1) (off + 64)
      (setBlockXorU m.size out (block key nonce ctr) m off h h hMN) hMN
  else if off < m.size then
    (tailXorSetU m off
      (pushBlock (ByteArray.emptyWithCapacity 64) (block key nonce ctr)) 0 out hMN).val
  else out.val
  termination_by m.size - off
  decreasing_by omega

theorem size_copyAll (msg : ByteArray) :
    (msg.copySlice 0 (ByteArray.emptyWithCapacity msg.size) 0 msg.size).size
      = msg.size := by
  rw [ByteArray.copySlice_eq_append]
  simp [ByteArray.size_append, ByteArray.size_extract, size_emptyWithCapacity,
    ByteArray.size_data]

/-- The retained `getElem`/`set` (boxed-`Nat`-indexed) fused pass — the previous
    `chacha20` body, kept as a differential baseline. `chacha20_eq_setPass`
    proves the guarded `chacha20` agrees with it. -/
def chacha20Set (key : Key) (nonce : Nonce) (counter : UInt32)
    (msg : ByteArray) : ByteArray :=
  chacha20SetGo key nonce msg counter 0
    ⟨msg.copySlice 0 (ByteArray.emptyWithCapacity msg.size) 0 msg.size,
     size_copyAll msg⟩

/-- Encrypt or decrypt a message (fused single pass, in-place XOR writes into
    a pre-sized copy of the message). Indexes with `uget`/`uset` when the
    message fits a `USize` (always, for any allocatable `ByteArray`), falling
    back to the `getElem`/`set` push pass otherwise. -/
def chacha20 (key : Key) (nonce : Nonce) (counter : UInt32)
    (msg : ByteArray) : ByteArray :=
  if hMN : msg.size < USize.size then
    chacha20SetGoU key nonce msg counter 0
      ⟨msg.copySlice 0 (ByteArray.emptyWithCapacity msg.size) 0 msg.size,
       size_copyAll msg⟩ hMN
  else
    chacha20Push key nonce counter msg

end ChaCha20.Fast
