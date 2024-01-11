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

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "c501f6b8fa2502362bf94678d404857e46e2b65d"

def run (cmd : String) (args : Array String) : ScriptM Bool := do
  let out ← IO.Process.output {
    cmd := cmd
    args := args
  }
  let hasError := out.exitCode != 0
  if hasError then
    IO.eprint out.stderr
  return hasError

script build do
  if ← run "lake exe mdgen" #["LeanSpec", "md"] then return 1
  return 0
