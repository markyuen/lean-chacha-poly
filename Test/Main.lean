import Test.Helpers
import Test.ChaCha20Test
import Test.Poly1305Test
import Test.ChaCha20Poly1305Test
import Test.PropertiesTest

def main : IO Unit := do
  IO.println "=== lean-chacha-poly test suite ==="
  IO.println "(RFC 8439 test vectors, ported 1:1 from the Go suite)"
  IO.println ""
  Test.ChaCha20Test.runTests
  Test.Poly1305Test.runTests
  Test.ChaCha20Poly1305Test.runTests
  Test.PropertiesTest.runTests
  IO.println "=== done ==="
