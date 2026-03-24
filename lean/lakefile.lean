import Lake
open Lake DSL

package «two-sorted-arith» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require std from git
  "https://github.com/leanprover/std4" @ "main"

@[default_target]
lean_lib TwoSortedArith where
  srcDir := "."
