import Lake
open Lake DSL

package «universal-principle» where
  name := "universal-principle"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.0"

@[default_target]
lean_lib «UniversalPrinciple» where
  roots := #[`UniversalPrinciple]
