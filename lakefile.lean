import Lake
open Lake DSL

package "ChompLean" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.0"

@[default_target]
lean_lib «ChompLean» where
  -- add library configuration options here
