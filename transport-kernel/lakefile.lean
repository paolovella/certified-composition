import Lake
open Lake DSL

package «transport-kernel»

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

require Physlib from git "https://github.com/leanprover-community/physlib.git" @ "af04d60bcd7618af849ff511e0a19d77f709937e"

require TransportCalculus from "../transport-calculus"

@[default_target]
lean_lib «TransportKernel»
