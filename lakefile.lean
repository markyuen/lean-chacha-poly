import Lake
open Lake DSL

package «lean-chacha-poly» where
  leanOptions := #[⟨`autoImplicit, false⟩]

lean_lib LeanChachaPoly

lean_lib Test where
  globs := #[.submodules `Test]

@[default_target]
lean_exe test where
  root := `Test.Main
