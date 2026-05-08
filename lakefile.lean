import Lake
open Lake DSL

package "opn"

@[default_target]
lean_lib «OPN-Proof1»

@[default_target]
lean_lib «OPN-Proof2»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"
