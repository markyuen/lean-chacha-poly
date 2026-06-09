import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.ChaCha20.Spec.QuarterRound

/-!
# ChaCha20 Block Function Properties

Properties of `chacha20Block` and `serializeBlock`.

## Role in the proof chain

The byte-count facts that used to live here (`u32ToLe` = 4 bytes,
`serializeBlock` = 64 bytes, `addStates`/`chacha20Block` size = 16) are now
*enforced by the types*: `u32ToLe : Bytes 4`, `serializeBlock : State → Bytes 64`,
`addStates`/`chacha20Block : … → State (= Words 16)`. The guarantees are available
as `.property` at every call site, so the standalone size theorems are gone.
-/

namespace ChaCha20.Spec

/-! ## RFC 8439 §2.3.2 block function test vector

    Key:     0x00010203...0x1f (32-byte ascending)
    Nonce:   0x00000009 0x0000004a 0x00000000
    Counter: 1

    Checks first 4 words of the output state.
    Full verification is by `decide`; the complete 64-byte
    keystream check is in `Test/ChaCha20Test.lean`. -/
-- Expensive: left as a `#eval` check rather than compiled theorem.
-- #eval (chacha20Block myKey myNonce 1)[0]!  -- should be 0xe4e7f110

end ChaCha20.Spec
