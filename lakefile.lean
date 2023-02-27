import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "main"

package «leanSpec» {
  -- add package configuration options here
}

lean_lib «LeanSpec» {
  -- add library configuration options here
}

@[default_target]
lean_exe «leanSpec» {
  root := `Main
}

def run (cmd : String) (args : Array String) : ScriptM Bool := do
  let out ← IO.Process.output {
    cmd := cmd
    args := args
  }
  let hasError := out.exitCode != 0
  if hasError then
    IO.eprint out.stderr
  return hasError

script md do
  let _ ← run "rm" #["-rf", "md"]

  if ← run "python3" #["-m", "lean2md", "LeanSpec", "md"] then return 1
  if ← run "python3" #["-m", "lean2md", "LeanSpec/lib", "md/lib"] then return 1
  if ← run "python3" #["-m", "lean2md", "LeanSpec/FPL", "md/FPL"] then return 1

  return 0