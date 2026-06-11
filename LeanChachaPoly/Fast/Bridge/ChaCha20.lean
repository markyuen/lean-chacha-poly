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

/-- **Engines agree.** The register-threaded rounds equal `rounds`. -/
theorem roundsGo_eq (n : Nat) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    roundsGo n x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      = rounds n ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩ := by
  induction n generalizing x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 with
  | zero => rfl
  | succ n ih =>
    rcases h1 : quarterRound x0 x4 x8 x12 with ⟨a1, b1, c1, d1⟩
    rcases h2 : quarterRound x1 x5 x9 x13 with ⟨a2, b2, c2, d2⟩
    rcases h3 : quarterRound x2 x6 x10 x14 with ⟨a3, b3, c3, d3⟩
    rcases h4 : quarterRound x3 x7 x11 x15 with ⟨a4, b4, c4, d4⟩
    rcases h5 : quarterRound a1 b2 c3 d4 with ⟨a5, b5, c5, d5⟩
    rcases h6 : quarterRound a2 b3 c4 d1 with ⟨a6, b6, c6, d6⟩
    rcases h7 : quarterRound a3 b4 c1 d2 with ⟨a7, b7, c7, d7⟩
    rcases h8 : quarterRound a4 b1 c2 d3 with ⟨a8, b8, c8, d8⟩
    rw [rounds]
    simp only [roundsGo, doubleRound, h1, h2, h3, h4, h5, h6, h7, h8]
    exact ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

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

/-- The fused block equals add-back-of-rounds on the initial state. -/
theorem block_eq_addSt_rounds (key : Key) (nonce : Nonce) (ctr : UInt32) :
    block key nonce ctr
      = addSt (rounds 10 (initSt key nonce ctr)) (initSt key nonce ctr) := by
  simp only [block, initSt, roundsGo_eq]
  rcases hr : rounds 10 (initSt key nonce ctr) with ⟨z0, z1, z2, z3, z4, z5, z6, z7,
    z8, z9, z10, z11, z12, z13, z14, z15⟩
  simp only [initSt] at hr
  rw [hr]
  rfl

/-- **Key lemma.** The fast block function matches `Spec.chacha20Block`. -/
theorem block_toState (key : Key) (nonce : Nonce) (ctr : UInt32) :
    (block key nonce ctr).toState
      = ChaCha20.Spec.chacha20Block key.toSpec nonce.toSpec ctr := by
  rw [block_eq_addSt_rounds, ChaCha20.Spec.chacha20Block, ChaCha20.Spec.tenDoubleRounds,
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

/-! ## Fused-pass bridge

The fused single-pass loop (`chacha20Go`) XORs each 64-byte keystream block
directly against the message. The bridge peels the spec keystream one block
at a time (`keystream_block_cons`), splits the spec XOR along the same
64-byte seams (`zipWith_block_split`, `zipWith_seg`), and matches each
4-byte `pushXor4` against one serialized word. -/

/-- One 64-byte block peels off the front of the spec keystream. -/
private theorem keystream_block_cons (k : ChaCha20.Spec.Key) (n : ChaCha20.Spec.Nonce)
    (ctr : UInt32) (len : Nat) (h : 64 ≤ len) :
    ChaCha20.Spec.keystream k n ctr len
      = (ChaCha20.Spec.serializeBlock (ChaCha20.Spec.chacha20Block k n ctr)).val
          ++ ChaCha20.Spec.keystream k n (ctr + 1) (len - 64) := by
  have hser : ∀ c : UInt32,
      ((ChaCha20.Spec.serializeBlock (ChaCha20.Spec.chacha20Block k n c)).val).length = 64 :=
    fun c => (ChaCha20.Spec.serializeBlock _).property
  rw [ChaCha20.Spec.keystream, ChaCha20.Spec.keystream]
  have hn : (len + 63) / 64 = (len - 64 + 63) / 64 + 1 := by omega
  rw [hn, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
    List.take_append, hser, List.take_of_length_le (by rw [hser]; exact h)]
  simp [uadd_shift, Nat.succ_eq_add_one]

/-- A keystream of at most one block is a `take` of the first block. -/
private theorem keystream_le_64 (k : ChaCha20.Spec.Key) (n : ChaCha20.Spec.Nonce)
    (ctr : UInt32) (len : Nat) (h : len ≤ 64) :
    ChaCha20.Spec.keystream k n ctr len
      = ((ChaCha20.Spec.serializeBlock (ChaCha20.Spec.chacha20Block k n ctr)).val).take len := by
  rw [ChaCha20.Spec.keystream]
  rcases Nat.eq_zero_or_pos len with h0 | h0
  · subst h0; simp
  · have hn : (len + 63) / 64 = 1 := by omega
    rw [hn]; simp

private theorem keystream_zero (k : ChaCha20.Spec.Key) (n : ChaCha20.Spec.Nonce)
    (ctr : UInt32) : ChaCha20.Spec.keystream k n ctr 0 = [] := rfl

/-- `zipWith` ignores second-list elements beyond the first list's length
    (not in core or Mathlib). -/
private theorem zipWith_take_right {α β γ : Type} (f : α → β → γ) :
    ∀ (l : List α) (l₂ : List β),
      List.zipWith f l (l₂.take l.length) = List.zipWith f l l₂
  | [], _ => by simp
  | _ :: l, [] => by simp
  | a :: l, b :: l₂ => by simp [List.zipWith_cons_cons, zipWith_take_right f l l₂]

/-- A 4-byte slice of a `ByteArray`'s list view, as literal indexing. -/
private theorem slice4_eq (m : ByteArray) (i : Nat) (h : i + 4 ≤ m.size) :
    (m.data.toList.drop i).take 4
      = [m[i]'(by omega), m[i+1]'(by omega), m[i+2]'(by omega), m[i+3]'(by omega)] := by
  have h0 : i < m.data.toList.length := by simp; omega
  have h1 : i + 1 < m.data.toList.length := by simp; omega
  have h2 : i + 2 < m.data.toList.length := by simp; omega
  have h3 : i + 3 < m.data.toList.length := by simp; omega
  rw [List.drop_eq_getElem_cons h0, List.take_succ_cons,
      List.drop_eq_getElem_cons h1, List.take_succ_cons,
      List.drop_eq_getElem_cons h2, List.take_succ_cons,
      List.drop_eq_getElem_cons h3, List.take_succ_cons, List.take_zero]
  simp only [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data]
  rfl

/-- **Supporting.** Pushing 4 XORed bytes is appending the slice XOR the
    word's LE bytes. -/
theorem pushXor4_toList (acc : ByteArray) (w : UInt32) (m : ByteArray) (i : Nat)
    (h : i + 4 ≤ m.size) :
    (pushXor4 acc w m i h).data.toList
      = acc.data.toList
        ++ List.zipWith (· ^^^ ·) ((m.data.toList.drop i).take 4)
            (ChaCha20.Spec.u32ToLe w).val := by
  rw [slice4_eq m i h]
  simp [pushXor4, ChaCha20.Spec.u32ToLe, byte0]

/-- Split a `zipWith` over a 4-byte left segment. `n`, `m`, `off'` are
    explicit with equation hypotheses so every offset stays in flat
    `off + 4k` form matching `pushBlockXor`'s literal offsets. -/
private theorem zipWith_seg {f : UInt8 → UInt8 → UInt8} {l : List UInt8} {off : Nat}
    (n m : Nat) (off' : Nat) (hnm : n = 4 + m) (hoff : off' = off + 4)
    {a b : List UInt8} (ha : a.length = 4) (h : off + 4 ≤ l.length) :
    List.zipWith f ((l.drop off).take n) (a ++ b)
      = List.zipWith f ((l.drop off).take 4) a
        ++ List.zipWith f ((l.drop off').take m) b := by
  subst hnm; subst hoff
  rw [List.take_add, List.drop_drop,
    List.zipWith_append (by simp [List.length_take, ha]; omega)]

/-- **Key lemma.** Pushing a XORed block is appending the 64-byte message
    slice XOR the serialized state. -/
theorem pushBlockXor_toList (acc : ByteArray) (s : St) (m : ByteArray) (off : Nat)
    (h : off + 64 ≤ m.size) :
    (pushBlockXor acc s m off h).data.toList
      = acc.data.toList
        ++ List.zipWith (· ^^^ ·) ((m.data.toList.drop off).take 64)
            (ChaCha20.Spec.serializeBlock s.toState).val := by
  obtain ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ := s
  have hL : off + 64 ≤ m.data.toList.length := by simp; omega
  simp only [ChaCha20.Spec.serializeBlock, St.toState,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [zipWith_seg 64 60 (off+4)  rfl (by omega) (ChaCha20.Spec.u32ToLe x0).property  (by omega),
      zipWith_seg 60 56 (off+8)  rfl (by omega) (ChaCha20.Spec.u32ToLe x1).property  (by omega),
      zipWith_seg 56 52 (off+12) rfl (by omega) (ChaCha20.Spec.u32ToLe x2).property  (by omega),
      zipWith_seg 52 48 (off+16) rfl (by omega) (ChaCha20.Spec.u32ToLe x3).property  (by omega),
      zipWith_seg 48 44 (off+20) rfl (by omega) (ChaCha20.Spec.u32ToLe x4).property  (by omega),
      zipWith_seg 44 40 (off+24) rfl (by omega) (ChaCha20.Spec.u32ToLe x5).property  (by omega),
      zipWith_seg 40 36 (off+28) rfl (by omega) (ChaCha20.Spec.u32ToLe x6).property  (by omega),
      zipWith_seg 36 32 (off+32) rfl (by omega) (ChaCha20.Spec.u32ToLe x7).property  (by omega),
      zipWith_seg 32 28 (off+36) rfl (by omega) (ChaCha20.Spec.u32ToLe x8).property  (by omega),
      zipWith_seg 28 24 (off+40) rfl (by omega) (ChaCha20.Spec.u32ToLe x9).property  (by omega),
      zipWith_seg 24 20 (off+44) rfl (by omega) (ChaCha20.Spec.u32ToLe x10).property (by omega),
      zipWith_seg 20 16 (off+48) rfl (by omega) (ChaCha20.Spec.u32ToLe x11).property (by omega),
      zipWith_seg 16 12 (off+52) rfl (by omega) (ChaCha20.Spec.u32ToLe x12).property (by omega),
      zipWith_seg 12 8  (off+56) rfl (by omega) (ChaCha20.Spec.u32ToLe x13).property (by omega),
      zipWith_seg 8  4  (off+60) rfl (by omega) (ChaCha20.Spec.u32ToLe x14).property (by omega)]
  simp only [pushBlockXor, pushXor4_toList, List.append_assoc]

/-- **Supporting.** The tail-XOR loop appends the element-wise XOR of the
    message suffix and the keystream suffix. -/
theorem tailXor_go_toList (m : ByteArray) (off : Nat) (ks : ByteArray) (j : Nat)
    (acc : ByteArray) :
    (tailXor.go m off ks j acc).data.toList
      = acc.data.toList
        ++ List.zipWith (· ^^^ ·) (m.data.toList.drop (off + j))
            (ks.data.toList.drop j) := by
  fun_induction ChaCha20.Fast.tailXor.go with
  | case1 j acc h ih =>
    rw [ih,
      List.drop_eq_getElem_cons (l := m.data.toList) (i := off + j) (by simpa using h.1),
      List.drop_eq_getElem_cons (l := ks.data.toList) (i := j) (by simpa using h.2),
      List.zipWith_cons_cons]
    simp only [Nat.add_assoc, ByteArray.getElem_eq_getElem_data, Array.getElem_toList,
      toList_push, List.append_assoc, List.cons_append, List.nil_append]
    rfl
  | case2 j acc h =>
    rw [Decidable.not_and_iff_not_or_not] at h
    rcases h with h | h
    · rw [List.drop_eq_nil_of_le (as := m.data.toList) (by simp; omega)]
      simp
    · rw [List.drop_eq_nil_of_le (as := ks.data.toList) (by simp; omega)]
      simp

/-- **Supporting.** `tailXor` XORs the message tail against the keystream. -/
theorem tailXor_toList (acc m : ByteArray) (off : Nat) (ks : ByteArray) :
    (tailXor acc m off ks).data.toList
      = acc.data.toList
        ++ List.zipWith (· ^^^ ·) (m.data.toList.drop off) ks.data.toList := by
  rw [tailXor, tailXor_go_toList]; simp

/-- Split a `zipWith` along a 64-byte second-list segment. -/
private theorem zipWith_block_split (l a b : List UInt8) (ha : a.length = 64)
    (hl : 64 ≤ l.length) :
    List.zipWith (· ^^^ ·) l (a ++ b)
      = List.zipWith (· ^^^ ·) (l.take 64) a
        ++ List.zipWith (· ^^^ ·) (l.drop 64) b := by
  conv => lhs; rw [← List.take_append_drop 64 l]
  rw [List.zipWith_append (by simp [List.length_take, ha]; omega)]

/-- **Key lemma.** The fused loop appends the spec XOR of the message suffix
    with the keystream for the remaining length. -/
theorem chacha20Go_toList (key : Key) (nonce : Nonce) (m : ByteArray)
    (ctr : UInt32) (off : Nat) (acc : ByteArray) :
    (chacha20Go key nonce m ctr off acc).data.toList
      = acc.data.toList
        ++ ChaCha20.Spec.xorBytes (m.data.toList.drop off)
            (ChaCha20.Spec.keystream key.toSpec nonce.toSpec ctr (m.size - off)) := by
  fun_induction ChaCha20.Fast.chacha20Go with
  | case1 ctr off acc h ih =>
    rw [ih, pushBlockXor_toList, block_toState]
    have hsplit : ChaCha20.Spec.xorBytes (m.data.toList.drop off)
          (ChaCha20.Spec.keystream key.toSpec nonce.toSpec ctr (m.size - off))
        = List.zipWith (· ^^^ ·) ((m.data.toList.drop off).take 64)
            (ChaCha20.Spec.serializeBlock
              (ChaCha20.Spec.chacha20Block key.toSpec nonce.toSpec ctr)).val
          ++ ChaCha20.Spec.xorBytes (m.data.toList.drop (off + 64))
              (ChaCha20.Spec.keystream key.toSpec nonce.toSpec (ctr + 1)
                (m.size - (off + 64))) := by
      rw [keystream_block_cons _ _ _ _ (by omega),
        show m.size - off - 64 = m.size - (off + 64) by omega,
        ChaCha20.Spec.xorBytes, ChaCha20.Spec.xorBytes,
        zipWith_block_split _ _ _ (ChaCha20.Spec.serializeBlock _).property (by simp; omega),
        List.drop_drop]
    rw [hsplit, List.append_assoc]
  | case2 ctr off acc h hlt =>
    rw [tailXor_toList, pushBlock_toList, block_toState, toList_emptyWithCapacity,
      List.nil_append, keystream_le_64 _ _ _ _ (by omega),
      show m.size - off = (m.data.toList.drop off).length by simp,
      ChaCha20.Spec.xorBytes, zipWith_take_right]
  | case3 ctr off acc h hlt =>
    rw [show m.size - off = 0 by omega, keystream_zero]
    simp [ChaCha20.Spec.xorBytes]

/-! ## Set-pass bridge

The in-place writer is proved by "splicing": `toList_set` turns each
`ByteArray.set` into `List.set`, `set4_splice` turns four consecutive sets
into a `take ++ segment ++ drop` splice, and `splice_step` composes the 16
word splices at flat offsets, carrying each accumulated segment's length so
no per-step length side conditions are needed. -/

/-- `set` through the `(·.data.toList)` view. -/
theorem toList_set (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) :
    (a.set i v h).data.toList = a.data.toList.set i v := by
  rw [ByteArray.data_set, Array.toList_set]

/-- Four consecutive `set`s splice a 4-element segment into the list. -/
private theorem set4_splice (L : List UInt8) (i : Nat) (a b c d : UInt8)
    (h : i + 4 ≤ L.length) :
    (((L.set i a).set (i+1) b).set (i+2) c).set (i+3) d
      = L.take i ++ [a, b, c, d] ++ L.drop (i + 4) := by
  have ht : (L.take i).length = i := by simp [List.length_take]; omega
  have s1 : L.set i a = L.take i ++ a :: L.drop (i+1) := by
    rw [List.set_eq_take_append_cons_drop, if_pos (by omega)]
  have s2 : (L.take i ++ a :: L.drop (i+1)).set (i+1) b
      = L.take i ++ a :: b :: L.drop (i+2) := by
    rw [List.set_append_right _ _ (by omega), ht, Nat.add_sub_cancel_left,
      List.set_cons_succ, List.drop_eq_getElem_cons (by omega : i + 1 < L.length),
      List.set_cons_zero]
  have s3 : (L.take i ++ a :: b :: L.drop (i+2)).set (i+2) c
      = L.take i ++ a :: b :: c :: L.drop (i+3) := by
    rw [List.set_append_right _ _ (by omega), ht, Nat.add_sub_cancel_left,
      List.set_cons_succ, List.set_cons_succ,
      List.drop_eq_getElem_cons (by omega : i + 2 < L.length), List.set_cons_zero]
  have s4 : (L.take i ++ a :: b :: c :: L.drop (i+3)).set (i+3) d
      = L.take i ++ a :: b :: c :: d :: L.drop (i+4) := by
    rw [List.set_append_right _ _ (by omega), ht, Nat.add_sub_cancel_left,
      List.set_cons_succ, List.set_cons_succ, List.set_cons_succ,
      List.drop_eq_getElem_cons (by omega : i + 3 < L.length), List.set_cons_zero]
  rw [s1, s2, s3, s4]
  simp

/-- **Supporting.** `setXor4` splices 4 XORed bytes into the output. -/
theorem setXor4_toList (n : Nat) (out : SizedBA n) (w : UInt32) (m : ByteArray)
    (i : Nat) (hm : i + 4 ≤ m.size) (ho : i + 4 ≤ n) :
    (setXor4 n out w m i hm ho).val.data.toList
      = out.val.data.toList.take i
        ++ List.zipWith (· ^^^ ·) ((m.data.toList.drop i).take 4)
            (ChaCha20.Spec.u32ToLe w).val
        ++ out.val.data.toList.drop (i + 4) := by
  have hsz := out.property
  rw [slice4_eq m i hm]
  simp only [setXor4, toList_set]
  rw [set4_splice _ _ _ _ _ _ (by simp; omega)]
  simp [ChaCha20.Spec.u32ToLe, byte0]

/-- Compose one `setXor4` splice onto an accumulated splice at flat offsets.
    The segment length is carried in the conclusion so each step's hypotheses
    come from the previous step's conclusion (no per-step length proofs). -/
private theorem splice_step {n : Nat} {out ok : SizedBA n} {P : List UInt8}
    {off p : Nat} (i q : Nat) (w : UInt32) {m : ByteArray}
    (hk : ok.val.data.toList
            = out.val.data.toList.take off ++ P ++ out.val.data.toList.drop i
          ∧ P.length = p)
    (hi : i = off + p) (hq : q = i + 4)
    (hm : i + 4 ≤ m.size) (ho : i + 4 ≤ n) :
    (setXor4 n ok w m i hm ho).val.data.toList
        = out.val.data.toList.take off
          ++ (P ++ List.zipWith (· ^^^ ·) ((m.data.toList.drop i).take 4)
                (ChaCha20.Spec.u32ToLe w).val)
          ++ out.val.data.toList.drop q
      ∧ (P ++ List.zipWith (· ^^^ ·) ((m.data.toList.drop i).take 4)
            (ChaCha20.Spec.u32ToLe w).val).length = p + 4 := by
  have hsz := out.property
  obtain ⟨hk, hP⟩ := hk
  subst hi hq
  have hZ : (List.zipWith (· ^^^ ·) ((m.data.toList.drop (off + p)).take 4)
      (ChaCha20.Spec.u32ToLe w).val).length = 4 := by
    simp [List.length_zipWith, List.length_take,
      (ChaCha20.Spec.u32ToLe w).property]
    omega
  refine ⟨?_, by simp [hP, hZ]⟩
  rw [setXor4_toList n ok w m _ hm ho, hk]
  have hAP : (out.val.data.toList.take off ++ P).length = off + p := by
    simp [List.length_take, hP]
    omega
  have hd : List.drop (off + p + 4)
      (out.val.data.toList.take off ++ P ++ out.val.data.toList.drop (off + p))
      = out.val.data.toList.drop (off + p + 4) := by
    rw [← List.drop_drop, List.drop_left' hAP, List.drop_drop]
  rw [List.take_left' hAP, hd]
  simp [List.append_assoc]

/-- **Key lemma.** `setBlockXor` splices the 64-byte message-XOR-keystream
    segment into the output at `off`. -/
theorem setBlockXor_toList (n : Nat) (out : SizedBA n) (s : St) (m : ByteArray)
    (off : Nat) (hm : off + 64 ≤ m.size) (ho : off + 64 ≤ n) :
    (setBlockXor n out s m off hm ho).val.data.toList
      = out.val.data.toList.take off
        ++ List.zipWith (· ^^^ ·) ((m.data.toList.drop off).take 64)
            (ChaCha20.Spec.serializeBlock s.toState).val
        ++ out.val.data.toList.drop (off + 64) := by
  obtain ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ := s
  have hsz := out.property
  have hL : off + 64 ≤ m.data.toList.length := by simp; omega
  have H0 : out.val.data.toList
        = out.val.data.toList.take off ++ [] ++ out.val.data.toList.drop off
      ∧ ([] : List UInt8).length = 0 := ⟨by simp, rfl⟩
  have H1 := splice_step off (off + 4) x0 H0 rfl rfl
    (le_of_off64' hm) (le_of_off64' ho)
  have H2 := splice_step (off + 4) (off + 8) x1 H1 rfl (Nat.add_assoc off 4 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H3 := splice_step (off + 8) (off + 12) x2 H2 rfl (Nat.add_assoc off 8 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H4 := splice_step (off + 12) (off + 16) x3 H3 rfl (Nat.add_assoc off 12 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H5 := splice_step (off + 16) (off + 20) x4 H4 rfl (Nat.add_assoc off 16 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H6 := splice_step (off + 20) (off + 24) x5 H5 rfl (Nat.add_assoc off 20 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H7 := splice_step (off + 24) (off + 28) x6 H6 rfl (Nat.add_assoc off 24 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H8 := splice_step (off + 28) (off + 32) x7 H7 rfl (Nat.add_assoc off 28 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H9 := splice_step (off + 32) (off + 36) x8 H8 rfl (Nat.add_assoc off 32 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H10 := splice_step (off + 36) (off + 40) x9 H9 rfl (Nat.add_assoc off 36 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H11 := splice_step (off + 40) (off + 44) x10 H10 rfl (Nat.add_assoc off 40 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H12 := splice_step (off + 44) (off + 48) x11 H11 rfl (Nat.add_assoc off 44 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H13 := splice_step (off + 48) (off + 52) x12 H12 rfl (Nat.add_assoc off 48 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H14 := splice_step (off + 52) (off + 56) x13 H13 rfl (Nat.add_assoc off 52 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H15 := splice_step (off + 56) (off + 60) x14 H14 rfl (Nat.add_assoc off 56 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  have H16 := splice_step (off + 60) (off + 64) x15 H15 rfl (Nat.add_assoc off 60 4).symm
    (le_of_off64 (by decide) hm) (le_of_off64 (by decide) ho)
  simp only [ChaCha20.Spec.serializeBlock, St.toState,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [
      zipWith_seg 64 60 (off+4) rfl rfl (ChaCha20.Spec.u32ToLe x0).property (le_of_off64' hL),
      zipWith_seg 60 56 (off+8) rfl (Nat.add_assoc off 4 4).symm (ChaCha20.Spec.u32ToLe x1).property (le_of_off64 (by decide) hL),
      zipWith_seg 56 52 (off+12) rfl (Nat.add_assoc off 8 4).symm (ChaCha20.Spec.u32ToLe x2).property (le_of_off64 (by decide) hL),
      zipWith_seg 52 48 (off+16) rfl (Nat.add_assoc off 12 4).symm (ChaCha20.Spec.u32ToLe x3).property (le_of_off64 (by decide) hL),
      zipWith_seg 48 44 (off+20) rfl (Nat.add_assoc off 16 4).symm (ChaCha20.Spec.u32ToLe x4).property (le_of_off64 (by decide) hL),
      zipWith_seg 44 40 (off+24) rfl (Nat.add_assoc off 20 4).symm (ChaCha20.Spec.u32ToLe x5).property (le_of_off64 (by decide) hL),
      zipWith_seg 40 36 (off+28) rfl (Nat.add_assoc off 24 4).symm (ChaCha20.Spec.u32ToLe x6).property (le_of_off64 (by decide) hL),
      zipWith_seg 36 32 (off+32) rfl (Nat.add_assoc off 28 4).symm (ChaCha20.Spec.u32ToLe x7).property (le_of_off64 (by decide) hL),
      zipWith_seg 32 28 (off+36) rfl (Nat.add_assoc off 32 4).symm (ChaCha20.Spec.u32ToLe x8).property (le_of_off64 (by decide) hL),
      zipWith_seg 28 24 (off+40) rfl (Nat.add_assoc off 36 4).symm (ChaCha20.Spec.u32ToLe x9).property (le_of_off64 (by decide) hL),
      zipWith_seg 24 20 (off+44) rfl (Nat.add_assoc off 40 4).symm (ChaCha20.Spec.u32ToLe x10).property (le_of_off64 (by decide) hL),
      zipWith_seg 20 16 (off+48) rfl (Nat.add_assoc off 44 4).symm (ChaCha20.Spec.u32ToLe x11).property (le_of_off64 (by decide) hL),
      zipWith_seg 16 12 (off+52) rfl (Nat.add_assoc off 48 4).symm (ChaCha20.Spec.u32ToLe x12).property (le_of_off64 (by decide) hL),
      zipWith_seg 12 8  (off+56) rfl (Nat.add_assoc off 52 4).symm (ChaCha20.Spec.u32ToLe x13).property (le_of_off64 (by decide) hL),
      zipWith_seg 8  4  (off+60) rfl (Nat.add_assoc off 56 4).symm (ChaCha20.Spec.u32ToLe x14).property (le_of_off64 (by decide) hL)]
  simp only [setBlockXor]
  rw [H16.1]
  simp [List.append_assoc]

/-- `take (k+1)` of a list `set` at `k` is `take k` plus the new element. -/
private theorem take_set_succ (L : List UInt8) (k : Nat) (v : UInt8)
    (h : k < L.length) :
    (L.set k v).take (k + 1) = L.take k ++ [v] := by
  rw [List.take_add_one, List.take_set,
    List.set_eq_of_length_le (by simp [List.length_take]; omega),
    List.getElem?_set_self (by omega)]
  rfl

/-- **Supporting.** The in-place tail XOR splices the element-wise XOR of the
    message suffix and the keystream suffix (the output suffix is fully
    overwritten when the keystream covers the message tail). -/
theorem tailXorSet_toList (m : ByteArray) (off : Nat) (ks : ByteArray) (j : Nat)
    (out : SizedBA m.size) (hks : m.size ≤ off + ks.size) :
    (tailXorSet m off ks j out).val.data.toList
      = out.val.data.toList.take (off + j)
        ++ List.zipWith (· ^^^ ·) (m.data.toList.drop (off + j))
            (ks.data.toList.drop j) := by
  fun_induction tailXorSet with
  | case1 j out h ih =>
    rw [ih]
    have hset : ∀ (v : UInt8) (hv),
        (⟨out.val.set (off + j) v hv, by rw [size_set]; exact out.property⟩
          : SizedBA m.size).val.data.toList.take (off + (j + 1))
        = out.val.data.toList.take (off + j) ++ [v] := by
      intro v hv
      rw [show off + (j + 1) = (off + j) + 1 by omega, toList_set,
        take_set_succ _ _ _ (by simp [out.property]; omega)]
    rw [hset]
    rw [List.drop_eq_getElem_cons (l := m.data.toList) (i := off + j) (by simpa using h.1),
      List.drop_eq_getElem_cons (l := ks.data.toList) (i := j) (by simpa using h.2),
      List.zipWith_cons_cons]
    simp only [Nat.add_assoc, ByteArray.getElem_eq_getElem_data, Array.getElem_toList,
      List.append_assoc, List.cons_append, List.nil_append]
    rfl
  | case2 j out h =>
    have hj : m.size ≤ off + j := by
      rw [Decidable.not_and_iff_not_or_not] at h
      rcases h with h | h <;> omega
    rw [List.drop_eq_nil_of_le (as := m.data.toList) (by simp; omega),
      List.take_of_length_le (by simp [out.property]; omega)]
    simp

/-- **Key lemma.** The set-based fused loop keeps the prefix `[0, off)` and
    overwrites the suffix with the spec XOR. -/
theorem chacha20SetGo_toList (key : Key) (nonce : Nonce) (m : ByteArray)
    (ctr : UInt32) (off : Nat) (out : SizedBA m.size) :
    (chacha20SetGo key nonce m ctr off out).data.toList
      = out.val.data.toList.take off
        ++ ChaCha20.Spec.xorBytes (m.data.toList.drop off)
            (ChaCha20.Spec.keystream key.toSpec nonce.toSpec ctr (m.size - off)) := by
  fun_induction chacha20SetGo with
  | case1 ctr off out h ih =>
    rw [ih]
    have ho := setBlockXor_toList m.size out (block key nonce ctr) m off h h
    rw [block_toState] at ho
    have hZlen : (List.zipWith (· ^^^ ·) ((m.data.toList.drop off).take 64)
        (ChaCha20.Spec.serializeBlock
          (ChaCha20.Spec.chacha20Block key.toSpec nonce.toSpec ctr)).val).length = 64 := by
      simp [List.length_zipWith, List.length_take,
        (ChaCha20.Spec.serializeBlock _).property]
      omega
    have htake : (setBlockXor m.size out (block key nonce ctr) m off h h).val.data.toList.take
          (off + 64)
        = out.val.data.toList.take off
          ++ List.zipWith (· ^^^ ·) ((m.data.toList.drop off).take 64)
              (ChaCha20.Spec.serializeBlock
                (ChaCha20.Spec.chacha20Block key.toSpec nonce.toSpec ctr)).val := by
      rw [ho]
      exact List.take_left' (by simp [List.length_take, hZlen, out.property]; omega)
    rw [htake]
    have hsplit : ChaCha20.Spec.xorBytes (m.data.toList.drop off)
          (ChaCha20.Spec.keystream key.toSpec nonce.toSpec ctr (m.size - off))
        = List.zipWith (· ^^^ ·) ((m.data.toList.drop off).take 64)
            (ChaCha20.Spec.serializeBlock
              (ChaCha20.Spec.chacha20Block key.toSpec nonce.toSpec ctr)).val
          ++ ChaCha20.Spec.xorBytes (m.data.toList.drop (off + 64))
              (ChaCha20.Spec.keystream key.toSpec nonce.toSpec (ctr + 1)
                (m.size - (off + 64))) := by
      rw [keystream_block_cons _ _ _ _ (by omega),
        show m.size - off - 64 = m.size - (off + 64) by omega,
        ChaCha20.Spec.xorBytes, ChaCha20.Spec.xorBytes,
        zipWith_block_split _ _ _ (ChaCha20.Spec.serializeBlock _).property (by simp; omega),
        List.drop_drop]
    rw [hsplit, List.append_assoc]
  | case2 ctr off out h hlt =>
    rw [tailXorSet_toList _ _ _ _ _
        (by rw [size_pushBlock, size_emptyWithCapacity]; omega),
      pushBlock_toList, block_toState, toList_emptyWithCapacity, List.nil_append,
      keystream_le_64 _ _ _ _ (by omega),
      show m.size - off = (m.data.toList.drop off).length by simp,
      ChaCha20.Spec.xorBytes, List.drop_zero, zipWith_take_right]
    simp
  | case3 ctr off out h hlt =>
    have hlen : out.val.data.toList.length ≤ off := by simp [out.property]; omega
    rw [show m.size - off = 0 by omega, keystream_zero,
      List.take_of_length_le hlen]
    simp [ChaCha20.Spec.xorBytes]

/-! ## USize engine equals the set engine

The `uget`/`uset` (USize-indexed) engine equals the `getElem`/`set`
(Nat-indexed) engine pointwise: `uget`/`uset` reduce to `getElem`/`set` at the
index's `Nat` value (`uget_eq_getElem`, `uset_eq_set`), and the `USize`
indices round-trip under the `m.size < USize.size` guard
(`toNat_toUSize_of_lt`). So `chacha20SetGoU` inherits `chacha20SetGo_toList`
and the capstone, with no new spec reasoning. -/

theorem setXor4U_eq (n : Nat) (out : SizedBA n) (w : UInt32) (m : ByteArray)
    (i : Nat) (iU : USize) (hiU : iU.toNat = i)
    (hm : i + 4 ≤ m.size) (ho : i + 4 ≤ n) (hMN : m.size < USize.size) :
    setXor4U n out w m i iU hiU hm ho hMN = setXor4 n out w m i hm ho := by
  apply Subtype.ext
  simp only [setXor4U, setXor4, uget_eq_getElem, uset_eq_set, Nat.add_zero,
    uidx_eq hiU (show i + 0 < USize.size by omega),
    uidx_eq hiU (show i + 1 < USize.size by omega),
    uidx_eq hiU (show i + 2 < USize.size by omega),
    uidx_eq hiU (show i + 3 < USize.size by omega)]

theorem setBlockXorU_eq (n : Nat) (out : SizedBA n) (s : St) (m : ByteArray) (off : Nat)
    (hm : off + 64 ≤ m.size) (ho : off + 64 ≤ n) (hMN : m.size < USize.size) :
    setBlockXorU n out s m off hm ho hMN = setBlockXor n out s m off hm ho := by
  simp only [setBlockXorU, setBlockXor, setXor4U_eq]

theorem tailXorSetU_eq (m : ByteArray) (off : Nat) (ks : ByteArray) (j : Nat)
    (out : SizedBA m.size) (hMN : m.size < USize.size) :
    tailXorSetU m off ks j out hMN = tailXorSet m off ks j out := by
  fun_induction tailXorSetU m off ks j out hMN with
  | case1 j out h ih =>
    rw [tailXorSet, dif_pos h, ih]
    congr 1
    apply Subtype.ext
    simp only [uset_eq_set, uget_eq_getElem,
      toNat_toUSize_of_lt (show off + j < USize.size by have := out.property; omega)]
  | case2 j out h =>
    rw [tailXorSet, dif_neg h]

theorem chacha20SetGoU_eq (key : Key) (nonce : Nonce) (m : ByteArray) (ctr : UInt32)
    (off : Nat) (out : SizedBA m.size) (hMN : m.size < USize.size) :
    chacha20SetGoU key nonce m ctr off out hMN = chacha20SetGo key nonce m ctr off out := by
  fun_induction chacha20SetGoU key nonce m ctr off out hMN with
  | case1 ctr off out h ih =>
    rw [chacha20SetGo, dif_pos h, ih, setBlockXorU_eq]
  | case2 ctr off out h hlt =>
    rw [chacha20SetGo, dif_neg h, if_pos hlt, tailXorSetU_eq]
  | case3 ctr off out h hlt =>
    rw [chacha20SetGo, dif_neg h, if_neg hlt]

/-! ## Capstone -/

/-- **Supporting.** The retained push-based pass also matches the spec
    (the previous capstone proof, verbatim). -/
theorem chacha20Push_toList (key : Key) (nonce : Nonce) (ctr : UInt32)
    (msg : ByteArray) :
    (chacha20Push key nonce ctr msg).data.toList
      = ChaCha20.Spec.chacha20 key.toSpec nonce.toSpec ctr msg.data.toList := by
  rw [chacha20Push, chacha20Go_toList, ChaCha20.Spec.chacha20]
  simp

/-- **Capstone.** The fast ChaCha20 equals the spec on every input:
    encrypting a `ByteArray` and reading the bytes back gives exactly the
    spec's output on the same bytes. Splits on the `msg.size < USize.size`
    guard: the `uget`/`uset` engine via `chacha20SetGoU_eq`, the fallback via
    `chacha20Push_toList`. -/
theorem chacha20_eq_spec (key : Key) (nonce : Nonce) (ctr : UInt32)
    (msg : ByteArray) :
    (chacha20 key nonce ctr msg).data.toList
      = ChaCha20.Spec.chacha20 key.toSpec nonce.toSpec ctr msg.data.toList := by
  rw [chacha20]
  split
  · rw [chacha20SetGoU_eq, chacha20SetGo_toList, ChaCha20.Spec.chacha20]
    simp
  · exact chacha20Push_toList key nonce ctr msg

/-- **Supporting.** The retained `getElem`/`set` pass also matches the spec
    (the previous capstone proof, verbatim). -/
theorem chacha20Set_toList (key : Key) (nonce : Nonce) (ctr : UInt32)
    (msg : ByteArray) :
    (chacha20Set key nonce ctr msg).data.toList
      = ChaCha20.Spec.chacha20 key.toSpec nonce.toSpec ctr msg.data.toList := by
  rw [chacha20Set, chacha20SetGo_toList, ChaCha20.Spec.chacha20]
  simp

/-- **Engines agree.** The guarded `uget`/`uset` pass equals the retained
    `getElem`/`set` pass. -/
theorem chacha20_eq_setPass (key : Key) (nonce : Nonce) (ctr : UInt32)
    (msg : ByteArray) :
    chacha20 key nonce ctr msg = chacha20Set key nonce ctr msg := by
  apply toList_inj
  rw [chacha20_eq_spec, chacha20Set_toList]

/-- **Engines agree.** The set-based pass equals the retained push-based pass. -/
theorem chacha20_eq_pushPass (key : Key) (nonce : Nonce) (ctr : UInt32)
    (msg : ByteArray) :
    chacha20 key nonce ctr msg = chacha20Push key nonce ctr msg := by
  apply toList_inj
  rw [chacha20_eq_spec, chacha20Push_toList]

/-- **Engines agree.** The fused pass equals the retained two-pass
    composition (XOR against a materialized keystream). -/
theorem chacha20_eq_twoPass (key : Key) (nonce : Nonce) (ctr : UInt32)
    (msg : ByteArray) :
    chacha20 key nonce ctr msg = xorBytes msg (keystream key nonce ctr msg.size) := by
  apply toList_inj
  rw [chacha20_eq_spec, xorBytes_toList, keystream_toList, ChaCha20.Spec.chacha20]
  simp

end ChaCha20.Fast
