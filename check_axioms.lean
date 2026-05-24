import Lean

open Lean Meta

structure CheckResult where
  ok : Bool
  usedTemporary : Bool

private def dotted (s : String) : Name :=
  s.toName

def checkedTheorems : List Name :=
  [ dotted "TaoExercises.TaoBook.Chapter2.exercise_2_3"
  , dotted "TaoExercises.TaoBook.Chapter2.exercise_2_6"
  , dotted "Erdos1.erdos_1.variants.weaker"
  , dotted "Erdos1.choose_middle_isEquivalent"
  , dotted "Erdos1.erdos_1_solution_axiom"
  , dotted "Erdos142.erdos_problem_142_iff_deepmind"
  , dotted "Erdos142.erdos_problem_142_explicit_iff_deepmind"
  , dotted "Erdos142.erdos_problem_142_solution_axiom"
  , dotted "Erdos142.erdos_problem_142_of_mainSplitGap_and_frontier"
  ]

def checkedModules : List String :=
  [ "SimpleExercises.Continuity" ]

/--
Load checked modules at runtime.
Avoiding large compile-time imports keeps the checker executable from eagerly initializing the
entire proof corpus before `main` starts.
-/
def checkedImports : Array Import :=
  #[ { module := dotted "TaoExercises.TaoBook.Chapter2.Exercise2_3" }
   , { module := dotted "TaoExercises.TaoBook.Chapter2.Exercise2_6" }
   , { module := dotted "SimpleExercises.Continuity" }
   , { module := dotted "Groups.HeisenbergGroup" }
   , { module := dotted "ErdosProblems.Problem1Literature" }
   , { module := dotted "ErdosProblems.Problem142Gap" }
   ]

def baseAxioms : Array Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

def temporaryAllowedAxioms : Array Name :=
  #[ dotted "Erdos1.erdos_1"
   , dotted "Erdos142.splitGap_k3_upper_exponent_gt_half_frontier"
   , dotted "Erdos142.splitGap_k4_profile_dominance_frontier"
   , dotted "Erdos142.splitGap_kge5_profile_dominance_frontier"
   , dotted "Heisenberg.theorem_1_1"
   ]

def timeIO (enabled : Bool) (label : String) (action : IO α) : IO α := do
  if enabled then
    let start ← IO.monoMsNow
    let result ← action
    let stop ← IO.monoMsNow
    IO.eprintln s!"[check_axioms] {label}: {(stop - start).toFloat / 1000.0}s"
    pure result
  else
    action

def collectAxiomsInEnv (env : Environment) (name : Name) : Array Name :=
  let (_, s) := ((Lean.CollectAxioms.collect name).run env).run {}
  s.axioms

def checkOne (env : Environment) (name : Name) : IO CheckResult := do
  let axioms := collectAxiomsInEnv env name

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

def isCheckableModuleDecl (env : Environment) (name : Name) : Bool :=
  if name.isInternalDetail then
    false
  else
    match env.find? name with
    | some (.defnInfo _) | some (.thmInfo _) | some (.axiomInfo _) | some (.opaqueInfo _) => true
    | _ => false

def moduleDecls (env : Environment) (moduleName : String) : Array Name :=
  env.const2ModIdx.fold
      (fun acc declName modIdx =>
        if env.header.moduleNames[modIdx.toNat]!.toString == moduleName &&
            isCheckableModuleDecl env declName then
          acc.push declName
        else
          acc)
      #[]
    |>.qsort Name.lt

def finish (profile : Bool) (mainStart : Nat) (code : UInt32) : IO UInt32 := do
  if profile then
    let stop ← IO.monoMsNow
    IO.eprintln s!"[check_axioms] main total: {(stop - mainStart).toFloat / 1000.0}s"
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit code.toUInt8

def loadEnv (profile : Bool) : IO Environment := do
  let sysroot ← timeIO profile "findSysroot" findSysroot
  let _ ← timeIO profile "initSearchPath" <| initSearchPath sysroot
  timeIO profile "importModules" <| importModules checkedImports {}

def exitCodeOfResult (result : CheckResult) : UInt32 :=
  if result.ok then
    if result.usedTemporary then 2 else 0
  else
    1

def runSingle (profile : Bool) (mainStart : Nat) (declName : Name) : IO UInt32 := do
  try
    let env ← loadEnv profile
    let result ← timeIO profile s!"check {declName}" <| checkOne env declName
    finish profile mainStart (exitCodeOfResult result)
  catch e =>
    IO.println s!"Error: {e}"
    finish profile mainStart 1

def runWorker (profile : Bool) (declName : Name) : IO CheckResult := do
  let out ← timeIO profile s!"worker {declName}" <|
    IO.Process.output { cmd := ".lake/build/bin/check_axioms", args := #["--single", toString declName] }
  IO.print out.stdout
  if !out.stderr.isEmpty then
    (← IO.getStderr).putStr out.stderr
  match out.exitCode with
  | 0 => pure ⟨true, false⟩
  | 2 => pure ⟨true, true⟩
  | 1 => pure ⟨false, false⟩
  | code => throw <| IO.userError s!"Worker for '{declName}' exited with unexpected code {code}."

def runAll (profile : Bool) (mainStart : Nat) : IO UInt32 := do
  try
    let env ← loadEnv profile
    let mut allOk := true
    let mut anyTemporary := false
    for name in checkedTheorems do
      let result ← runWorker profile name
      allOk := allOk && result.ok
      anyTemporary := anyTemporary || result.usedTemporary
    for moduleName in checkedModules do
      let decls ← timeIO profile s!"moduleDecls {moduleName}" <| pure (moduleDecls env moduleName)
      if decls.isEmpty then
        IO.println s!"✅ The module '{moduleName}' is included in the checker and currently has no checkable declarations."
      else
        for declName in decls do
          let result ← runWorker profile declName
          allOk := allOk && result.ok
          anyTemporary := anyTemporary || result.usedTemporary

    if allOk then
      if anyTemporary then
        IO.println
          "✅ All checked items are free of 'sorry'. Temporary Erdős #1/#142 axiom debt is explicitly allowed."
      else
        IO.println "✅ All checked solutions are free of 'sorry' and use only base axioms."
      finish profile mainStart 0
    else
      IO.println "❌ Base-axiom verification failed."
      finish profile mainStart 1
  catch e =>
    IO.println s!"Error: {e}"
    finish profile mainStart 1

def runListModuleDecls (profile : Bool) (mainStart : Nat) (moduleName : String) : IO UInt32 := do
  try
    let env ← loadEnv profile
    let decls ← timeIO profile s!"moduleDecls {moduleName}" <| pure (moduleDecls env moduleName)
    for declName in decls do
      IO.println s!"{declName}"
    finish profile mainStart 0
  catch e =>
    IO.println s!"Error: {e}"
    finish profile mainStart 1

def main (args : List String) : IO UInt32 := do
  let mainStart ← IO.monoMsNow
  let profile := (← IO.getEnv "CHECK_AXIOMS_PROFILE") == some "1"
  match args with
  | ["--single", declName] => runSingle profile mainStart (dotted declName)
  | ["--list-module-decls", moduleName] => runListModuleDecls profile mainStart moduleName
  | [] => runAll profile mainStart
  | _ =>
      IO.println "Usage: check_axioms [--single <declaration-name> | --list-module-decls <module-name>]"
      finish profile mainStart 1
