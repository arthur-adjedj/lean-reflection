import Lake
open Lake DSL

package «reflection» {
  -- add package configuration options here
}

require std from git "https://github.com/leanprover/std4" @ "v4.6.0-rc1"
require aesop from git "https://github.com/JLimperg/aesop" @ "v4.6.0-rc1"
-- require IIT from git "https://github.com/arthur-adjedj/iit" @ "v4.4.0"
require Qq from git "https://github.com/leanprover-community/quote4"

@[default_target]
lean_lib «Reflection» {
  -- add library configuration options here
}

-- lean_exe «reflection» {
--   root := `Main
-- }
