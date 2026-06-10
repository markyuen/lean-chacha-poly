import Tests.Helpers
import Tests.ChaCha20Test
import Tests.Poly1305Test
import Tests.ChaCha20Poly1305Test
import Tests.PropertiesTest
import Tests.FastTest

def main : IO Unit := do
  IO.println "=== lean-chacha-poly test suite ==="
  IO.println "(RFC 8439 test vectors, ported 1:1 from the Go suite)"
  IO.println ""
  Tests.ChaCha20Test.runTests
  Tests.Poly1305Test.runTests
  Tests.ChaCha20Poly1305Test.runTests
  Tests.PropertiesTest.runTests
  Tests.FastTest.runTests
  IO.println "=== done ==="
