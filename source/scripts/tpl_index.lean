import general
import Lean

open Lean Meta

structure TPLIndexEntry where
  name : String
  kind : String
  module : String
  statement : String
  doc : String
  dependencies : Array String
deriving ToJson

partial def collectConsts (e : Expr) (acc : Std.HashSet Name := {}) : Std.HashSet Name :=
  match e with
  | .const n _ => acc.insert n
  | .app f a => collectConsts a (collectConsts f acc)
  | .lam _ t b _ => collectConsts b (collectConsts t acc)
  | .forallE _ t b _ => collectConsts b (collectConsts t acc)
  | .letE _ t v b _ => collectConsts b (collectConsts v (collectConsts t acc))
  | .mdata _ b => collectConsts b acc
  | .proj _ _ b => collectConsts b acc
  | _ => acc

def declKind? : ConstantInfo → Option String
  | .defnInfo _ => some "def"
  | .opaqueInfo _ => some "def"
  | .thmInfo _ => some "theorem"
  | _ => none

def buildIndex : MetaM (Array TPLIndexEntry) := do
  let env ← getEnv
  let mut entries := #[]
  for name in env.const2ModIdx.keysArray do
    if name.isInternal then continue
    let some modIdx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[modIdx.toNat]!
    unless (`general == moduleName || (`general).isPrefixOf moduleName) do continue
    -- Keep source-level declarations and discard compiler-generated recursors,
    -- matchers, equation theorems, and similar implementation details.
    let some _ ← findDeclarationRangesCore? name | continue
    let some ci := env.find? name | continue
    let some kind := declKind? ci | continue
    let statement := (← ppExpr ci.type).pretty
    let doc := (← findDocString? env name).getD ""
    let dependencies := (collectConsts ci.type).toArray
      |>.filter (fun dep => dep != name)
      |>.map Name.toString
      |>.qsort (· < ·)
    entries := entries.push {
      name := name.toString
      kind
      module := moduleName.toString
      statement
      doc
      dependencies
    }
  return entries.qsort (fun a b => a.name < b.name)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `general }] {}
  let coreContext : Core.Context := {
    fileName := "<tpl-index>"
    fileMap := default
  }
  let coreState : Core.State := { env }
  let (entries, _, _) ← MetaM.toIO buildIndex coreContext coreState
  for entry in entries do
    IO.println (toJson entry).compress
  return 0
