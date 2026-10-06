import Lake
open Lake DSL

package «OPN» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

@[default_target]
lean_lib «OPN-Proof1» where
  srcDir := "."

lean_lib «OPN-Proof2» where
  srcDir := "."
