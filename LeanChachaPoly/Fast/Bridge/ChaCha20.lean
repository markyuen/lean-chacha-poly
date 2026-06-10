import LeanChachaPoly.Fast.ChaCha20
import LeanChachaPoly.Fast.Bridge.ByteList

/-!
# Fast bridge — ChaCha20

Proves the fast `ByteArray` ChaCha20 equal to `ChaCha20.Spec.chacha20`
(capstone `chacha20_eq_spec`).

The round-function bridge never reasons about ARX semantics: the fast
`doubleRound` applies the *same* `Spec.quarterRound` terms in the same
order, so each of the eight quarter-round positions is discharged by a
"stuck match" observation — `Spec.qr` on a literal 16-element state is
definitionally a match on `quarterRound` whose branches are fully reduced
array updates (`qr_0_4_8_12` …), and destructuring the eight
`quarterRound` results turns both sides into the same literal state.
-/

namespace ChaCha20.Fast

open ChaCha20.Spec (quarterRound)
open Fast.Bridge

/-! ## Quarter-round positions: `Spec.qr` on a literal state -/

private theorem qr_0_4_8_12 {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 a b c d : UInt32}
    (h : quarterRound x0 x4 x8 x12 = (a, b, c, d)) :
    ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨0, by omega⟩ ⟨4, by omega⟩ ⟨8, by omega⟩ ⟨12, by omega⟩
      = ⟨#[a,x1,x2,x3,b,x5,x6,x7,c,x9,x10,x11,d,x13,x14,x15], rfl⟩ := by
  have hstuck : ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨0, by omega⟩ ⟨4, by omega⟩ ⟨8, by omega⟩ ⟨12, by omega⟩
      = match quarterRound x0 x4 x8 x12 with
        | (a, b, c, d) =>
          (⟨#[a,x1,x2,x3,b,x5,x6,x7,c,x9,x10,x11,d,x13,x14,x15], rfl⟩ : ChaCha20.Spec.State) := rfl
  rw [hstuck, h]

private theorem qr_1_5_9_13 {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 a b c d : UInt32}
    (h : quarterRound x1 x5 x9 x13 = (a, b, c, d)) :
    ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨1, by omega⟩ ⟨5, by omega⟩ ⟨9, by omega⟩ ⟨13, by omega⟩
      = ⟨#[x0,a,x2,x3,x4,b,x6,x7,x8,c,x10,x11,x12,d,x14,x15], rfl⟩ := by
  have hstuck : ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨1, by omega⟩ ⟨5, by omega⟩ ⟨9, by omega⟩ ⟨13, by omega⟩
      = match quarterRound x1 x5 x9 x13 with
        | (a, b, c, d) =>
          (⟨#[x0,a,x2,x3,x4,b,x6,x7,x8,c,x10,x11,x12,d,x14,x15], rfl⟩ : ChaCha20.Spec.State) := rfl
  rw [hstuck, h]

private theorem qr_2_6_10_14 {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 a b c d : UInt32}
    (h : quarterRound x2 x6 x10 x14 = (a, b, c, d)) :
    ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨2, by omega⟩ ⟨6, by omega⟩ ⟨10, by omega⟩ ⟨14, by omega⟩
      = ⟨#[x0,x1,a,x3,x4,x5,b,x7,x8,x9,c,x11,x12,x13,d,x15], rfl⟩ := by
  have hstuck : ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨2, by omega⟩ ⟨6, by omega⟩ ⟨10, by omega⟩ ⟨14, by omega⟩
      = match quarterRound x2 x6 x10 x14 with
        | (a, b, c, d) =>
          (⟨#[x0,x1,a,x3,x4,x5,b,x7,x8,x9,c,x11,x12,x13,d,x15], rfl⟩ : ChaCha20.Spec.State) := rfl
  rw [hstuck, h]

private theorem qr_3_7_11_15 {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 a b c d : UInt32}
    (h : quarterRound x3 x7 x11 x15 = (a, b, c, d)) :
    ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨3, by omega⟩ ⟨7, by omega⟩ ⟨11, by omega⟩ ⟨15, by omega⟩
      = ⟨#[x0,x1,x2,a,x4,x5,x6,b,x8,x9,x10,c,x12,x13,x14,d], rfl⟩ := by
  have hstuck : ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨3, by omega⟩ ⟨7, by omega⟩ ⟨11, by omega⟩ ⟨15, by omega⟩
      = match quarterRound x3 x7 x11 x15 with
        | (a, b, c, d) =>
          (⟨#[x0,x1,x2,a,x4,x5,x6,b,x8,x9,x10,c,x12,x13,x14,d], rfl⟩ : ChaCha20.Spec.State) := rfl
  rw [hstuck, h]

private theorem qr_0_5_10_15 {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 a b c d : UInt32}
    (h : quarterRound x0 x5 x10 x15 = (a, b, c, d)) :
    ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨0, by omega⟩ ⟨5, by omega⟩ ⟨10, by omega⟩ ⟨15, by omega⟩
      = ⟨#[a,x1,x2,x3,x4,b,x6,x7,x8,x9,c,x11,x12,x13,x14,d], rfl⟩ := by
  have hstuck : ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨0, by omega⟩ ⟨5, by omega⟩ ⟨10, by omega⟩ ⟨15, by omega⟩
      = match quarterRound x0 x5 x10 x15 with
        | (a, b, c, d) =>
          (⟨#[a,x1,x2,x3,x4,b,x6,x7,x8,x9,c,x11,x12,x13,x14,d], rfl⟩ : ChaCha20.Spec.State) := rfl
  rw [hstuck, h]

private theorem qr_1_6_11_12 {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 a b c d : UInt32}
    (h : quarterRound x1 x6 x11 x12 = (a, b, c, d)) :
    ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨1, by omega⟩ ⟨6, by omega⟩ ⟨11, by omega⟩ ⟨12, by omega⟩
      = ⟨#[x0,a,x2,x3,x4,x5,b,x7,x8,x9,x10,c,d,x13,x14,x15], rfl⟩ := by
  have hstuck : ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨1, by omega⟩ ⟨6, by omega⟩ ⟨11, by omega⟩ ⟨12, by omega⟩
      = match quarterRound x1 x6 x11 x12 with
        | (a, b, c, d) =>
          (⟨#[x0,a,x2,x3,x4,x5,b,x7,x8,x9,x10,c,d,x13,x14,x15], rfl⟩ : ChaCha20.Spec.State) := rfl
  rw [hstuck, h]

private theorem qr_2_7_8_13 {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 a b c d : UInt32}
    (h : quarterRound x2 x7 x8 x13 = (a, b, c, d)) :
    ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨2, by omega⟩ ⟨7, by omega⟩ ⟨8, by omega⟩ ⟨13, by omega⟩
      = ⟨#[x0,x1,a,x3,x4,x5,x6,b,c,x9,x10,x11,x12,d,x14,x15], rfl⟩ := by
  have hstuck : ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨2, by omega⟩ ⟨7, by omega⟩ ⟨8, by omega⟩ ⟨13, by omega⟩
      = match quarterRound x2 x7 x8 x13 with
        | (a, b, c, d) =>
          (⟨#[x0,x1,a,x3,x4,x5,x6,b,c,x9,x10,x11,x12,d,x14,x15], rfl⟩ : ChaCha20.Spec.State) := rfl
  rw [hstuck, h]

private theorem qr_3_4_9_14 {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 a b c d : UInt32}
    (h : quarterRound x3 x4 x9 x14 = (a, b, c, d)) :
    ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨3, by omega⟩ ⟨4, by omega⟩ ⟨9, by omega⟩ ⟨14, by omega⟩
      = ⟨#[x0,x1,x2,a,b,x5,x6,x7,x8,c,x10,x11,x12,x13,d,x15], rfl⟩ := by
  have hstuck : ChaCha20.Spec.qr ⟨#[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15], rfl⟩
        ⟨3, by omega⟩ ⟨4, by omega⟩ ⟨9, by omega⟩ ⟨14, by omega⟩
      = match quarterRound x3 x4 x9 x14 with
        | (a, b, c, d) =>
          (⟨#[x0,x1,x2,a,b,x5,x6,x7,x8,c,x10,x11,x12,x13,d,x15], rfl⟩ : ChaCha20.Spec.State) := rfl
  rw [hstuck, h]
/-! ## Round bridge -/

/-- **Key lemma.** The unrolled fast double-round matches the spec's. -/
theorem doubleRound_toState (s : St) :
    (doubleRound s).toState = ChaCha20.Spec.doubleRound s.toState := by
  obtain ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ := s
  rcases h1 : quarterRound x0 x4 x8 x12 with ⟨a1,b1,c1,d1⟩
  rcases h2 : quarterRound x1 x5 x9 x13 with ⟨a2,b2,c2,d2⟩
  rcases h3 : quarterRound x2 x6 x10 x14 with ⟨a3,b3,c3,d3⟩
  rcases h4 : quarterRound x3 x7 x11 x15 with ⟨a4,b4,c4,d4⟩
  rcases h5 : quarterRound a1 b2 c3 d4 with ⟨a5,b5,c5,d5⟩
  rcases h6 : quarterRound a2 b3 c4 d1 with ⟨a6,b6,c6,d6⟩
  rcases h7 : quarterRound a3 b4 c1 d2 with ⟨a7,b7,c7,d7⟩
  rcases h8 : quarterRound a4 b1 c2 d3 with ⟨a8,b8,c8,d8⟩
  simp only [doubleRound, ChaCha20.Spec.doubleRound, St.toState,
    h1, h2, h3, h4, h5, h6, h7, h8]
  rw [qr_0_4_8_12 h1, qr_1_5_9_13 h2, qr_2_6_10_14 h3, qr_3_7_11_15 h4,
      qr_0_5_10_15 h5, qr_1_6_11_12 h6, qr_2_7_8_13 h7, qr_3_4_9_14 h8]

/-- **Supporting.** `rounds n` matches an `n`-fold spec double-round. -/
theorem rounds_toState (n : Nat) (s : St) :
    (rounds n s).toState
      = (List.replicate n ()).foldl (fun acc _ => ChaCha20.Spec.doubleRound acc) s.toState := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [rounds, List.replicate_succ, List.foldl_cons, ih, doubleRound_toState]

/-- **Supporting.** Word-wise state addition matches `Spec.addStates`. -/
theorem addSt_toState (a b : St) :
    (addSt a b).toState = ChaCha20.Spec.addStates a.toState b.toState := by
  apply Subtype.ext
  apply Array.toList_inj.mp
  simp [addSt, St.toState, ChaCha20.Spec.addStates]

/-! ## State initialization bridge -/

/-- **Supporting.** The fast state initialization matches `Spec.initState`. -/
theorem initSt_toState (key : Key) (nonce : Nonce) (ctr : UInt32) :
    (initSt key nonce ctr).toState
      = ChaCha20.Spec.initState key.toSpec nonce.toSpec ctr := by
  have hk : ∀ (i : Nat) (h : i < 32),
      key.val.data[i]?.getD default = key.val[i]'(by rw [key.property]; exact h) := by
    intro i h
    rw [Array.getElem?_eq_getElem (by simp [ByteArray.size_data ▸ key.property]; omega)]
    simp only [Option.getD_some, ByteArray.getElem_eq_getElem_data]
    rfl
  have hn : ∀ (i : Nat) (h : i < 12),
      nonce.val.data[i]?.getD default = nonce.val[i]'(by rw [nonce.property]; exact h) := by
    intro i h
    rw [Array.getElem?_eq_getElem (by simp [ByteArray.size_data ▸ nonce.property]; omega)]
    simp only [Option.getD_some, ByteArray.getElem_eq_getElem_data]
    rfl
  apply Subtype.ext
  simp [initSt, St.toState, Fast.BytesA.get, ChaCha20.Spec.initState,
    ChaCha20.Spec.magic, Fast.BytesA.toSpec, hk, hn]

/-- **Key lemma.** The fast block function matches `Spec.chacha20Block`. -/
theorem block_toState (key : Key) (nonce : Nonce) (ctr : UInt32) :
    (block key nonce ctr).toState
      = ChaCha20.Spec.chacha20Block key.toSpec nonce.toSpec ctr := by
  rw [block, ChaCha20.Spec.chacha20Block, ChaCha20.Spec.tenDoubleRounds,
    addSt_toState, rounds_toState, initSt_toState]

/-! ## Serialization bridge -/

private theorem byte0 (w : UInt32) : w.toUInt8 = UInt8.ofNat (w.toNat % 256) := by
  apply UInt8.toNat_inj.mp
  simp

/-- **Supporting.** Pushing a word is appending its LE bytes. -/
theorem pushU32le_toList (acc : ByteArray) (w : UInt32) :
    (pushU32le acc w).data.toList
      = acc.data.toList ++ (ChaCha20.Spec.u32ToLe w).val := by
  simp [pushU32le, ChaCha20.Spec.u32ToLe, byte0]

/-- **Key lemma.** Pushing a state is appending its 64 serialized bytes. -/
theorem pushBlock_toList (acc : ByteArray) (s : St) :
    (pushBlock acc s).data.toList
      = acc.data.toList ++ (ChaCha20.Spec.serializeBlock s.toState).val := by
  simp [pushBlock, pushU32le_toList, ChaCha20.Spec.serializeBlock, St.toState]

/-! ## Keystream bridge -/

private theorem uadd_shift (ctr x : UInt32) :
    ctr + 1 + x = ctr + (x + 1) := by
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_add]
  omega

/-- **Key lemma.** The keystream block loop appends the spec's block stream. -/
theorem keystreamGo_toList (key : Key) (nonce : Nonce) (n : Nat) (ctr : UInt32)
    (acc : ByteArray) :
    (keystreamGo key nonce n ctr acc).data.toList
      = acc.data.toList ++ (List.range n).flatMap (fun i =>
          (ChaCha20.Spec.serializeBlock
            (ChaCha20.Spec.chacha20Block key.toSpec nonce.toSpec
              (ctr + UInt32.ofNat i))).val) := by
  induction n generalizing ctr acc with
  | zero => simp [keystreamGo]
  | succ n ih =>
    rw [keystreamGo, ih, pushBlock_toList, block_toState, List.range_succ_eq_map]
    simp [List.flatMap_cons, List.flatMap_map, uadd_shift, Nat.succ_eq_add_one]

/-- **Key lemma.** The fast keystream matches `Spec.keystream`. -/
theorem keystream_toList (key : Key) (nonce : Nonce) (ctr : UInt32) (len : Nat) :
    (keystream key nonce ctr len).data.toList
      = ChaCha20.Spec.keystream key.toSpec nonce.toSpec ctr len := by
  rw [keystream, ChaCha20.Spec.keystream]
  simp [keystreamGo_toList]

/-! ## XOR bridge -/

/-- **Supporting.** The XOR loop appends the element-wise XOR of the suffixes. -/
theorem xorBytes_go_toList (a b : ByteArray) (i : Nat) (acc : ByteArray) :
    (xorBytes.go a b i acc).data.toList
      = acc.data.toList
        ++ List.zipWith (· ^^^ ·) (a.data.toList.drop i) (b.data.toList.drop i) := by
  fun_induction ChaCha20.Fast.xorBytes.go with
  | case1 i acc h ih =>
    rw [ih,
      List.drop_eq_getElem_cons (l := a.data.toList) (i := i) (by simpa using h.1),
      List.drop_eq_getElem_cons (l := b.data.toList) (i := i) (by simpa using h.2),
      List.zipWith_cons_cons]
    simp only [ByteArray.getElem_eq_getElem_data, Array.getElem_toList, toList_push,
      List.append_assoc, List.cons_append, List.nil_append]
    rfl
  | case2 i acc h =>
    rw [Decidable.not_and_iff_not_or_not] at h
    rcases h with h | h
    · rw [List.drop_eq_nil_of_le (as := a.data.toList) (by simp; omega)]
      simp
    · rw [List.drop_eq_nil_of_le (as := b.data.toList) (by simp; omega)]
      simp

/-- **Key lemma.** The fast XOR matches `Spec.xorBytes`. -/
theorem xorBytes_toList (a b : ByteArray) :
    (xorBytes a b).data.toList
      = ChaCha20.Spec.xorBytes a.data.toList b.data.toList := by
  rw [xorBytes, ChaCha20.Spec.xorBytes, xorBytes_go_toList]
  simp

/-! ## Capstone -/

/-- **Capstone.** The fast ChaCha20 equals the spec on every input:
    encrypting a `ByteArray` and reading the bytes back gives exactly the
    spec's output on the same bytes. -/
theorem chacha20_eq_spec (key : Key) (nonce : Nonce) (ctr : UInt32)
    (msg : ByteArray) :
    (chacha20 key nonce ctr msg).data.toList
      = ChaCha20.Spec.chacha20 key.toSpec nonce.toSpec ctr msg.data.toList := by
  rw [chacha20, ChaCha20.Spec.chacha20, xorBytes_toList, keystream_toList]
  simp

end ChaCha20.Fast
