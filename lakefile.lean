import Lake
open Lake DSL

package «reflection» {
  -- add package configuration options here
}

-- require aesop from git "https://github.com/leanprover-community/aesop" -- 01cb707de69cf88733addfff0bacc710efae8d20
require std from git "https://github.com/leanprover/std4" @ "v4.5.0-rc1"
require aesop from git "https://github.com/JLimperg/aesop" @ "v4.5.0-rc1"

@[default_target]
lean_lib «Reflection» {
  -- add library configuration options here
}

-- lean_exe «reflection» {
--   root := `Main
-- }
