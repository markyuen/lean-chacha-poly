import Lake
open Lake DSL

package «lean-chacha-poly» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib LeanChachaPoly

/- Includes `Tests.AxiomGuard`, whose `#guard_msgs` checks fail the build if any
   capstone's axiom set changes. It lives in the library (not the `test` exe):
   the guard imports the full `LeanChachaPoly` umbrella, and linking that (with
   Mathlib) into an executable is neither needed nor feasible — the guard is a
   purely compile-time check. -/
@[default_target]
lean_lib Tests where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe test where
  root := `Tests.Main
