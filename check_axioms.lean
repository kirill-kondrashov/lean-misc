import TaoExercises.TaoBook.Chapter2.Exercise2_3
import TaoExercises.TaoBook.Chapter2.Exercise2_6
import ErdosProblems.Problem142
import ErdosProblems.Problem142Literature
import Lean

open Lean Meta

structure CheckResult where
  ok : Bool
  usedTemporary : Bool

def checkedTheorems : List Name :=
  [ ``TaoExercises.TaoBook.Chapter2.exercise_2_3
  , ``TaoExercises.TaoBook.Chapter2.exercise_2_6
  , ``Erdos142.erdos_problem_142_iff_deepmind
  , ``Erdos142.erdos_problem_142_solution_axiom
  ]

def baseAxioms : Array Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

def temporaryAllowedAxioms : Array Name :=
  #[ ``Erdos142.erdos_problem_142_k3_upper_profile_bound_axiom
   , ``Erdos142.erdos_problem_142_k3_lower_profile_bound_axiom
   , ``Erdos142.erdos_problem_142_k4_case_axiom
   , ``Erdos142.erdos_problem_142_kge5_case_axiom
   ]

def checkOne (env : Environment) (name : Name) : IO CheckResult := do
  let coreContext : Core.Context := { fileName := "<check_axioms>", fileMap := default }
  let coreState : Core.State := { env := env }
  let metaM : MetaM (Array Name) := Lean.collectAxioms name

  let ((axioms, _), _) ←
    (metaM.run).run coreContext coreState |>.toIO (fun _ => IO.userError "Axiom check failed")

  let hasSorry := axioms.contains ``sorryAx
  let nonBase := axioms.filter (fun ax => !baseAxioms.contains ax && ax != ``sorryAx)
  let temporary := nonBase.filter (fun ax => temporaryAllowedAxioms.contains ax)
  let forbidden := nonBase.filter (fun ax => !temporaryAllowedAxioms.contains ax)
  let ok := !hasSorry && forbidden.isEmpty
  let usedTemporary := !temporary.isEmpty

  if ok && !usedTemporary then
    IO.println s!"✅ The proof of '{name}' is free of 'sorry' and uses only base axioms."
  else if ok && usedTemporary then
    IO.println s!"🟡 The proof of '{name}' is free of 'sorry' but relies on temporary allowed axiom debt."
  else
    IO.println s!"❌ The proof of '{name}' failed the base-axiom check."

  IO.println "Axioms used:"
  for ax in axioms.toList do
    IO.println s!"- {ax}"

  if hasSorry then
    IO.println "Found forbidden axiom: sorryAx"
  if !temporary.isEmpty then
    IO.println "Temporarily allowed non-base axioms (must be proved later):"
    for ax in temporary.toList do
      IO.println s!"- {ax}"
  if !forbidden.isEmpty then
    IO.println "Found non-base axioms:"
    for ax in forbidden.toList do
      IO.println s!"- {ax}"

  pure ⟨ok, usedTemporary⟩

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[ { module := `TaoExercises.TaoBook.Chapter2.Exercise2_3 }
     , { module := `TaoExercises.TaoBook.Chapter2.Exercise2_6 }
     , { module := `ErdosProblems.Problem142 }
     , { module := `ErdosProblems.Problem142Literature }
     ]
    {}

  try
    let mut allOk := true
    let mut anyTemporary := false
    for name in checkedTheorems do
      let result ← checkOne env name
      allOk := allOk && result.ok
      anyTemporary := anyTemporary || result.usedTemporary

    if allOk then
      if anyTemporary then
        IO.println "✅ All checked items are free of 'sorry'. Temporary Erdős #142 axiom debt is explicitly allowed."
      else
        IO.println "✅ All checked solutions are free of 'sorry' and use only base axioms."
      return (0 : UInt32)
    else
      IO.println "❌ Base-axiom verification failed."
      return (1 : UInt32)
  catch e =>
    IO.println s!"Error: {e}"
    return (1 : UInt32)
