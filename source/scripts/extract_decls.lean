import TrainingData.Frontend

open Lean Elab IO

structure DeclData where
  kind : String
  source : String
deriving ToJson, FromJson

def addStep (data : String × List DeclData) (step : CompilationStep) :
    IO (String × List DeclData) := do
  let (context, prev) := data
  let src := step.src.toString
  let newConsts ← step.newDecls2
  let next ← newConsts.filterMapM fun ci => step.runMetaMBefore do
    let kind ← match ci with
      | .defnInfo _ => pure (some "def")
      | .thmInfo _  => pure (some "theorem")
      | _ => pure none
    match kind with
    | none => return none
    | some k => return some ⟨k, src⟩
  return (context ++ src, next ++ prev)

def main (args : List String) : IO UInt32 := do
  let some moduleName := args[0]?
    | do IO.eprintln "Usage: extract_decls <ModuleName>"; return 1
  initSearchPath (← findSysroot)
  Lean.searchPathRef.modify fun sp => sp ++ [⟨"."⟩]
  let module := moduleName.toName
  let steps ← compileModule module
  let (_, data) ← steps.foldlM (init := ("", [])) addStep
  IO.println <| toString (toJson data)
  return 0
