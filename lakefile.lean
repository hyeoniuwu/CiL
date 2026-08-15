import Lake
open Lake DSL

abbrev mathlibOnlyLinters : Array LeanOption := #[
  ⟨`linter.mathlibStandardSet, true⟩,
  ⟨`linter.style.header, true⟩,
  ⟨`linter.checkInitImports, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
]

abbrev mathlibLeanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
  ] ++
    mathlibOnlyLinters.map fun s ↦ { s with name := `weak ++ s.name }

package «computability» where
  lintDriver := "batteries/runLinter"
  lintDriverArgs := #["Computability"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Computability» where
  leanOptions := mathlibLeanOptions
