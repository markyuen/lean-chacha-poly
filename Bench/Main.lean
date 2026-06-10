import LeanChachaPoly.ChaCha20.Spec
import LeanChachaPoly.Poly1305.Spec
import LeanChachaPoly.Aead.Spec
import LeanChachaPoly.Fast.Aead

/-!
# Benchmark suite

Throughput benchmarks for the fast (`ByteArray`) implementation against the
executable spec, across message sizes. Run locally with `lake exe bench`;
CI builds this executable (it is a default target) but does not run it —
shared-runner timings are noise.

Methodology:
- `IO.monoNanosNow` around a hot loop; a few warmup iterations first.
- Deterministic pseudo-random inputs (splitmix-style per-index hash).
- Every iteration's result contributes one byte to a checksum that is
  printed at the end, so the compiler cannot eliminate the work.
- The ChaCha20/AEAD closures take the iteration index as the block counter,
  so no two iterations compute identical values.
- Spec inputs are converted to `List UInt8` *outside* the timed region.
- The spec is run only up to 64 KiB (it is the verification artifact, not a
  production path).
-/

namespace Bench

/-! ## Deterministic inputs -/

def mix (x : UInt64) : UInt64 :=
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

def randByte (seed : UInt64) (i : Nat) : UInt8 :=
  (mix (seed + UInt64.ofNat i) >>> 56).toUInt8

def randList (seed : UInt64) (n : Nat) : List UInt8 :=
  (List.range n).map (randByte seed)

def randBA (seed : UInt64) (n : Nat) : ByteArray :=
  (randList seed n).toByteArray

def randBytesA (seed : UInt64) (n : Nat) : Fast.BytesA n :=
  ⟨(randList seed n).toByteArray, by simp [randList]⟩

/-! ## Harness -/

def pad (s : String) (n : Nat) : String :=
  s ++ String.ofList (List.replicate (n - s.length) ' ')

def padL (s : String) (n : Nat) : String :=
  String.ofList (List.replicate (n - s.length) ' ') ++ s

def fmtSize (bytes : Nat) : String :=
  if bytes % (1024 * 1024) == 0 && bytes > 0 then s!"{bytes / (1024 * 1024)} MiB"
  else if bytes % 1024 == 0 && bytes > 0 then s!"{bytes / 1024} KiB"
  else s!"{bytes} B"

/-- Time `iters` calls of `act` (after 3 warmup calls); print one table row;
    return a checksum so the work cannot be optimized away. -/
def row (name : String) (bytes iters : Nat) (act : Nat → UInt8) : IO UInt64 := do
  let mut sink : UInt64 := 0
  for i in [0:3] do
    sink := sink + (act i).toUInt64
  let t0 ← IO.monoNanosNow
  for i in [0:iters] do
    sink := sink + (act i).toUInt64
  let t1 ← IO.monoNanosNow
  let ns := t1 - t0
  let nsOp := ns / iters
  let mbps := if ns == 0 then 0 else bytes * iters * 1000 / ns
  IO.println s!"  {pad name 22} {padL (fmtSize bytes) 8} {padL (toString iters) 8} {padL (toString nsOp) 12} {padL (toString mbps) 8}"
  return sink

end Bench

open Bench

def main : IO Unit := do
  -- Inputs (spec-side lists built once, outside any timed region)
  let key   := randBytesA 1 32
  let nonce := randBytesA 2 12
  let pkey  := randBytesA 3 32
  let skey : ChaCha20.Spec.Key := key.toSpec
  let snonce : ChaCha20.Spec.Nonce := nonce.toSpec
  let spkey : Poly1305.Spec.Key := pkey.toSpec
  let aad := randBA 4 32

  let sizes : List (Nat × Nat × Nat) :=  -- (bytes, fast iters, spec iters)
    [(64, 100000, 2000), (1024, 20000, 200), (64 * 1024, 500, 5), (1024 * 1024, 32, 0)]

  IO.println "=== lean-chacha-poly benchmarks ==="
  IO.println s!"  {pad "name" 22} {padL "size" 8} {padL "iters" 8} {padL "ns/op" 12} {padL "MB/s" 8}"
  let mut sink : UInt64 := 0

  -- ChaCha20
  for (bytes, fIters, sIters) in sizes do
    let m := randBA (UInt64.ofNat (100 + bytes)) bytes
    sink := sink + (← row "chacha20 fast" bytes fIters
      (fun i => (ChaCha20.Fast.chacha20 key nonce (UInt32.ofNat i) m).get! 0))
    sink := sink + (← row "chacha20 fast 2pass" bytes fIters
      (fun i => (ChaCha20.Fast.xorBytes m
        (ChaCha20.Fast.keystream key nonce (UInt32.ofNat i) m.size)).get! 0))
    if sIters > 0 then
      let ml := m.data.toList
      sink := sink + (← row "chacha20 spec" bytes sIters
        (fun i => (ChaCha20.Spec.chacha20 skey snonce (UInt32.ofNat i) ml).headD 0))

  -- Poly1305
  let rN := Poly1305.Fast.extractR pkey
  for (bytes, fIters, sIters) in sizes do
    let m := randBA (UInt64.ofNat (200 + bytes)) bytes
    sink := sink + (← row "poly1305 fast" bytes fIters
      (fun _ => (Poly1305.Fast.poly1305 pkey m).get! 0))
    sink := sink + (← row "poly1305 fast nat" bytes fIters
      (fun _ => UInt8.ofNat (Poly1305.Fast.accumulateNat rN m % 256)))
    if sIters > 0 then
      let ml := m.data.toList
      sink := sink + (← row "poly1305 spec" bytes sIters
        (fun _ => (Poly1305.Spec.poly1305 spkey ml).val.headD 0))

  -- AEAD
  for (bytes, fIters, sIters) in sizes do
    let m := randBA (UInt64.ofNat (300 + bytes)) bytes
    let aeadIters := fIters / 2
    sink := sink + (← row "aead encrypt fast" bytes aeadIters
      (fun _ => (Aead.Fast.encrypt key nonce m aad).get! 0))
    let ct := Aead.Fast.encrypt key nonce m aad
    sink := sink + (← row "aead decrypt fast" bytes aeadIters
      (fun _ => match Aead.Fast.decrypt key nonce ct aad with
        | some pt => if h : 0 < pt.size then pt[0]'h else 1
        | none => 0))
    if sIters > 0 then
      let ml := m.data.toList
      let saad := aad.data.toList
      sink := sink + (← row "aead encrypt spec" bytes sIters
        (fun _ => (Aead.Spec.encrypt skey snonce ml saad).headD 0))
      let sct := Aead.Spec.encrypt skey snonce ml saad
      sink := sink + (← row "aead decrypt spec" bytes sIters
        (fun _ => match Aead.Spec.decrypt skey snonce sct saad with
          | some pt => pt.headD 1
          | none => 0))

  IO.println s!"  checksum: {sink}"
