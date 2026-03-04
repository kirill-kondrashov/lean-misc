import TaoExercises.TaoBook.Chapter2.Exercise2_3
import Lean

open Lean Meta

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `TaoExercises.TaoBook.Chapter2.Exercise2_3 }] {}

  let name := ``TaoExercises.TaoBook.Chapter2.exercise_2_3

  let coreContext : Core.Context := { fileName := "<check_axioms>", fileMap := default }
  let coreState : Core.State := { env := env }

  let metaM : MetaM (Array Name) := Lean.collectAxioms name

  try
    let ((axioms, _), _) ←
      (metaM.run).run coreContext coreState |>.toIO (fun _ => IO.userError "Axiom check failed")

    if axioms.contains ``sorryAx then
      IO.println s!"The proof of '{name}' relies on 'sorry'."
      return (1 : UInt32)
    else
      IO.println s!"The proof of '{name}' is free of 'sorry'."
      IO.println "Axioms used:"
      for ax in axioms.toList do
        IO.println s!"- {ax}"
      return (0 : UInt32)
  catch e =>
    IO.println s!"Error: {e}"
    return (1 : UInt32)
