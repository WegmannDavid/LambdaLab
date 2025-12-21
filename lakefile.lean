import Lake
open Lake DSL

set_option linter.unusedVariables false

package LambdaLab where
  -- add package configuration options here

lean_lib LambdaLab where
  -- add library configuration options here

@[default_target]
lean_exe stlc where
  root := `Main
