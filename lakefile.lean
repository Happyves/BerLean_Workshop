import Lake
open Lake DSL

package «workshop» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Workshop» {
  -- add any library configuration options here
}
