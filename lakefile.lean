import Lake
open Lake DSL

package «CHS» where
  -- add package configuration options here

lean_lib MathlibExtras
lean_lib «CHS» where
  -- add library configuration options here
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"

@[default_target]
lean_exe «chs» where
  root := `Main
