import LeanChachaPoly.ChaCha20.Spec.Keystream
import Mathlib

/-!
# ChaCha20 CTR Seekability

`keystream_counter_shift`: the keystream at a shifted counter equals the tail of
a longer keystream — i.e. ChaCha20 in counter mode is *seekable* / random-access.
The counter indexes 64-byte blocks consistently.
-/

namespace ChaCha20.Spec

/-- **Supporting.** The keystream from counter `ctr + offset` over `len` bytes is the tail
    (after `offset·64` bytes) of the keystream from `ctr` over `len + offset·64`
    bytes. Dropping `offset·64` bytes = skipping `offset` whole 64-byte blocks. -/
theorem keystream_counter_shift (key : Key) (nonce : Nonce)
    (ctr : UInt32) (len offset : Nat) :
    keystream key nonce (ctr + UInt32.ofNat offset) len =
    (keystream key nonce ctr (len + offset * 64)).drop (offset * 64) := by
  simp only [keystream]
  have hnR : (len + offset * 64 + 63) / 64 = offset + (len + 63) / 64 := by omega
  rw [hnR, List.range_add, List.flatMap_append]
  have hAlen : ((List.range offset).flatMap
      (fun i => (serializeBlock (chacha20Block key nonce (ctr + UInt32.ofNat i))).val)).length
      = offset * 64 := blockStream_length key nonce ctr offset
  have hmap : (List.map (fun x => offset + x) (List.range ((len + 63) / 64))).flatMap
      (fun i => (serializeBlock (chacha20Block key nonce (ctr + UInt32.ofNat i))).val)
      = (List.range ((len + 63) / 64)).flatMap
          (fun i => (serializeBlock
            (chacha20Block key nonce ((ctr + UInt32.ofNat offset) + UInt32.ofNat i))).val) := by
    rw [List.flatMap_map]; apply List.flatMap_congr; intro x _
    congr 3; rw [UInt32.ofNat_add, add_assoc]
  rw [hmap,
    show len + offset * 64 = ((List.range offset).flatMap
        (fun i => (serializeBlock (chacha20Block key nonce (ctr + UInt32.ofNat i))).val)).length + len
      from by rw [hAlen]; ring,
    show offset * 64 = ((List.range offset).flatMap
        (fun i => (serializeBlock (chacha20Block key nonce (ctr + UInt32.ofNat i))).val)).length
      from hAlen.symm,
    List.drop_take]
  simp

end ChaCha20.Spec
