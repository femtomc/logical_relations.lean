import Lake
open Lake DSL

package «intro_logical_relations» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «IntroLogicalRelations» {
  -- add any library configuration options here
}
