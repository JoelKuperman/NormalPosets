import Lake
open Lake DSL

package «normal_posets» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «NormalPosets» {
  -- add any library configuration options here
}
