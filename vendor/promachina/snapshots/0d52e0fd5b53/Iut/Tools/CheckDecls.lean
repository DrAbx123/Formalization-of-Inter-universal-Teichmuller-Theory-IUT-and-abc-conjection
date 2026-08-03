import Iut.Basic
import Iut.SourceTrace.IUTIVPaperLedger
import Iut.Stage1.IUTStage1Experiments
import Iut.Stage1.IUTStage1StepXIDependencyAudit

namespace Iut.Tools.CheckDecls

def usage : String :=
  "usage: lake exe checkdecls <lean_decls>"

def cleanLine (line : String) : Option String :=
  let line := line.trimAscii.toString
  if line.isEmpty || line.startsWith "#" then
    none
  else
    some line

def leanInput (decls : Array String) : String := Id.run do
  let mut input :=
    "import Iut.Basic\n\
    import Iut.SourceTrace.IUTIVPaperLedger\n\
    import Iut.Stage1.IUTStage1Experiments\n\
    import Iut.Stage1.IUTStage1StepXIDependencyAudit\n"
  for decl in decls do
    input := input ++ s!"#check {decl}\n"
  return input

def run (args : List String) : IO UInt32 := do
  let path ←
    match args with
    | [path] => pure path
    | _ =>
        IO.eprintln usage
        return 1
  let blueprintDecls := (← IO.FS.lines ⟨path⟩).filterMap cleanLine
  if blueprintDecls.isEmpty then
    IO.eprintln s!"no Lean declarations found in {path}"
    return 1
  let decls :=
    blueprintDecls ++ Iut.SourceTrace.iutIVOwnedDeclarations.toArray
  let output ← IO.Process.output {
    cmd := "lean"
    args := #["--stdin"]
  } (some (leanInput decls))
  IO.print output.stdout
  if output.exitCode == 0 then
    return 0
  else
    IO.eprint output.stderr
    return output.exitCode

end Iut.Tools.CheckDecls

def main (args : List String) : IO UInt32 :=
  Iut.Tools.CheckDecls.run args
