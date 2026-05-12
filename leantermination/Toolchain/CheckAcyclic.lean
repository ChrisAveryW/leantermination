import leantermination.Parsing.ITSParse
import leantermination.Parsing.Preparse
import leantermination.Termination.termination_lasw
import leantermination.Termination.AcyclicIntegerProgram

set_option linter.unusedVariables false
set_option linter.style.longLine false


def runZ3 (smt : String) : IO String := do
  -- write the smt string to a temp file
  let path := "/tmp/query.smt"
  IO.FS.writeFile path smt
  -- run z3 on it
  let out ← IO.Process.run
    { cmd  := "z3", args := #[path] }
  return out

def main : IO Unit := do
  let input ← IO.FS.readFile "leantermination/Data/IntegerPrograms/Acyclic/Test2.ari"
  match parseITS input with
  | some its =>
    IO.println s!"The provided Integer Program is represented like this:"
    IO.println s!"------------------------------------------------------"
    IO.println (reprStr its)
    IO.println s!"------------------------------------------------------"
    IO.println s!"The provided Integer Program is {(if IntegerProgram.isAcyclic its then "acyclic, thus terminates" else "non-acyclic, thus termination cannot be proven.")}"
  | none     => IO.println "Failed to parse ITS file"
