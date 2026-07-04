import Lake
open Lake DSL

package «transport-kernel»

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

require Physlib from git "https://github.com/leanprover-community/physlib.git" @ "2e21835a8fd5304fbf62f4d68ae4385272292e00"

@[default_target]
lean_lib «TransportKernel»
