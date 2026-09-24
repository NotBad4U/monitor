import Lake

open Lake DSL

package «Mealy» where version := v!"0.1.0"

lean_lib «Mealy»

@[default_target] lean_exe «mealy» where root := `Main

require "leanprover-community" / "mathlib"

require «lean-fmt» from git "https://github.com/jcreinhold/lean-fmt"@"v4.34.0-rc2"
