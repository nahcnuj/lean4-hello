import Lake
open Lake DSL

package «lean4hello» where
  -- add package configuration options here

lean_lib «Lean4hello» where
  -- add library configuration options here

@[default_target]
lean_exe «lean4hello» where
  root := `Main

lean_exe «feline» where
  root := `FelineMain

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
