import Lake
open Lake DSL

package «reflection» {
  -- add package configuration options here
}

-- require std from git "https://github.com/leanprover/std4" @ "nightly-testing-2024-04-04"
require aesop from git "https://github.com/JLimperg/aesop" @ "v4.12.0"
-- require IIT from git "https://github.com/arthur-adjedj/iit" @ "v4.4.0"
-- require Qq from git "https://github.com/leanprover-community/quote4" @ "53156671405fbbd5402ed17a79bd129b961bd8d6"
-- require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"
-- require auto from git "https://github.com/leanprover-community/lean-auto" @ "v4.11.0" -- doesn't work from lean 4.8

@[default_target]
lean_lib «Reflection» {
  -- add library configuration options here
}

-- lean_exe «reflection» {
--   root := `Main
-- }
