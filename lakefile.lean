import Lake
open Lake DSL

package «lean-chacha-poly» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

lean_lib LeanChachaPoly

lean_lib Tests where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe test where
  root := `Tests.Main
