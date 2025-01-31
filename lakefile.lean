import Lake
open Lake DSL

package «axiomhunter» where
  -- add package configuration options here

lean_lib «AxiomHunter» where
  -- add library configuration options here

@[default_target]
lean_exe «axiomhunter» where
  root := `Main
