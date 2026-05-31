import leantermination.Parsing.ITSParse
import leantermination.Parsing.Preparse
import leantermination.Termination.termination_lasw
set_option linter.unusedVariables false
set_option linter.style.longLine false



/-
def main : IO Unit := do
  let input ← IO.FS.readFile "leantermination/Data/ip_test.ari"
  match parseITS input with
  | some its => IO.println (reprStr its)
  | none     => IO.println "Failed to parse ITS file"


def main : IO Unit := do
  let input ← IO.FS.readFile "leantermination/Data/ip_test.ari"
  match preParseITS input with
  | some its => IO.println (reprStr its)
  | none     => IO.println "Failed to parse ITS file"-/

def runZ3 (smt : String) : IO String := do
  -- write the smt2 string to a temp file
  let path := "/tmp/query.smt"
  IO.FS.writeFile path smt
  -- run z3 on it
  let out ← IO.Process.run
    { cmd  := "z3"
    , args := #[path] }
  return out

def test : Transition :=
  {src := 0, tgt := 0, guard := .atom .lt (.add (.var 0) (.var 1)) (.lit 5), update :=
  [{pv := 0, expr:= Expr.add (Expr.var 0) (Expr.var 1)},
  {pv := 1, expr:= Expr.sub (Expr.var 1) (Expr.var 2)},
  {pv := 2, expr:= Expr.add (Expr.var 2) (Expr.lit 4)}]}


def main : IO Unit := do
  let output := test.toSMT
  IO.println "Query:"
  IO.println output
  IO.println "Result:"
  let result ← runZ3 output
  IO.println result
