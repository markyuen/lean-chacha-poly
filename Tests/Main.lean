import Tests.Helpers
import Tests.ChaCha20Test
import Tests.Poly1305Test
import Tests.ChaCha20Poly1305Test
import Tests.PropertiesTest
import Tests.FastTest
import Tests.WycheproofTest

/-- Returns the process exit code: `0` if every check passed, `1` otherwise, so
    `lake exe test` (and CI) fails on a vector mismatch rather than only printing
    a `✗`. -/
def main : IO UInt32 := do
  IO.println "=== lean-chacha-poly test suite ==="
  IO.println "(RFC 8439 test vectors, ported 1:1 from the Go suite)"
  IO.println ""
  let mut fails := 0
  fails := fails + (← Tests.ChaCha20Test.runTests)
  fails := fails + (← Tests.Poly1305Test.runTests)
  fails := fails + (← Tests.ChaCha20Poly1305Test.runTests)
  fails := fails + (← Tests.PropertiesTest.runTests)
  fails := fails + (← Tests.FastTest.runTests)
  fails := fails + (← Tests.WycheproofTest.runTests)
  IO.println "=== done ==="
  if fails == 0 then
    IO.println "All checks passed."
    return 0
  else
    IO.eprintln s!"{fails} check(s) failed."
    return 1
