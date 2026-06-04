import Test.Helpers
import Test.ChaCha20Test
import Test.Poly1305Test
import Test.AeadTest

def main : IO Unit := do
  IO.println "=== lean-chacha-poly test suite ==="
  IO.println "(RFC 8439 test vectors)"
  IO.println ""
  Test.ChaCha20Test.runTests
  Test.Poly1305Test.runTests
  Test.AeadTest.runTests
  IO.println "=== done ==="
