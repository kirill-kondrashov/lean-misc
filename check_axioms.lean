import TaoExercises.TaoBook.Chapter2.Exercise2_3
import TaoExercises.TaoBook.Chapter2.Exercise2_6
import TaoExercises.ErdosProblems.Problem142
import Lean

open Lean Meta

def checkedTheorems : List Name :=
  [ ``TaoExercises.TaoBook.Chapter2.exercise_2_3
  , ``TaoExercises.TaoBook.Chapter2.exercise_2_6
  , ``Erdos142.erdos_problem_142_iff_deepmind
  ]

def baseAxioms : Array Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

def checkOne (env : Environment) (name : Name) : IO Bool := do
  let coreContext : Core.Context := { fileName := "<check_axioms>", fileMap := default }
  let coreState : Core.State := { env := env }
  let metaM : MetaM (Array Name) := Lean.collectAxioms name

  let ((axioms, _), _) ←
    (metaM.run).run coreContext coreState |>.toIO (fun _ => IO.userError "Axiom check failed")

  let hasSorry := axioms.contains ``sorryAx
  let nonBase := axioms.filter (fun ax => !baseAxioms.contains ax && ax != ``sorryAx)
  let ok := !hasSorry && nonBase.isEmpty

  if ok then
    IO.println s!"✅ The proof of '{name}' is free of 'sorry' and uses only base axioms."
  else
    IO.println s!"❌ The proof of '{name}' failed the base-axiom check."

  IO.println "Axioms used:"
  for ax in axioms.toList do
    IO.println s!"- {ax}"

  if hasSorry then
    IO.println "Found forbidden axiom: sorryAx"
  if !nonBase.isEmpty then
    IO.println "Found non-base axioms:"
    for ax in nonBase.toList do
      IO.println s!"- {ax}"

  pure ok

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[ { module := `TaoExercises.TaoBook.Chapter2.Exercise2_3 }
     , { module := `TaoExercises.TaoBook.Chapter2.Exercise2_6 }
     , { module := `TaoExercises.ErdosProblems.Problem142 }
     ]
    {}

  try
    let mut allOk := true
    for name in checkedTheorems do
      let ok ← checkOne env name
      allOk := allOk && ok

    if allOk then
      IO.println "✅ All checked solutions are free of 'sorry' and use only base axioms."
      return (0 : UInt32)
    else
      IO.println "❌ Base-axiom verification failed."
      return (1 : UInt32)
  catch e =>
    IO.println s!"Error: {e}"
    return (1 : UInt32)
