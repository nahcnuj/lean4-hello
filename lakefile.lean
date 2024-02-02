import Lake
open Lake DSL

package «lean4hello» where
  -- add package configuration options here

lean_lib «Lean4hello» where
  -- add library configuration options here

@[default_target]
lean_exe «lean4hello» where
  root := `Main
