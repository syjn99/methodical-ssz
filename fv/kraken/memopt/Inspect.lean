import Lean

/-!
# memopt inspector

Usage, from `fv/kraken/lean`:

    INSPECT_MOD=Fk.WitLcM4x16 lake env lean ../memopt/Inspect.lean > out.txt

This file imports only `Lean`. At `#eval` time it loads the `.olean` closure of
`INSPECT_MOD` with `importModules` and prints every constant that the `.olean` of
that module owns (`ModuleData.constNames`). The order is the sorted name order.

For each non-internal constant it prints: name, owner module, kind, level params,
the type with `pp.all true`, the type `Expr.hash`, the value `Expr.hash` for
definitions (not for theorem proofs), the sorted used constants of the type (and
of the value for definitions), and `collectAxioms`.

Internal constants (`Name.isInternalDetail`, for example `_proof_1`, `_simp_1`)
are listed by name and kind only, in a separate section. They come from proof
bodies and auxiliary elaboration.
-/

open Lean Meta

/-- With `loadExts := false`, `isInstanceCore` returned false for an `instance` in a test run.
So read the instance entries that the `.olean` of the owner module stores. -/
def isInst (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (instanceExtension.ext.getModuleEntries env i).any fun
      | .global e | .scoped _ e => e.globalName? == some n
  | none => false

def kindOf (env : Environment) (ci : ConstantInfo) : String :=
  let base := match ci with
    | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
    | .ctorInfo _ => "ctor" | .recInfo _ => "recursor"
  let red := match getReducibilityStatusCore env ci.name with
    | .reducible => " reducible" | .irreducible => " irreducible" | _ => ""
  let inst := if isInst env ci.name then " instance" else ""
  base ++ red ++ inst

def sortNames (a : Array Name) : Array Name :=
  (a.qsort Name.lt).toList.eraseDups.toArray

def inspect (mod : Name) : MetaM Unit := do
  let env ← importModules #[{ module := mod }] {} (loadExts := false)
  setEnv env
  let some idx := env.getModuleIdx? mod | throwError "module {mod} not found"
  let names := sortNames env.header.moduleData[idx.toNat]!.constNames
  let (internal, pub) := names.partition (·.isInternalDetail)
  IO.println s!"module: {mod}"
  IO.println s!"constants: {names.size} (public {pub.size}, internal {internal.size})"
  withTheReader Core.Context (fun c => { c with options := c.options.setBool `pp.all true }) do
    for n in pub do
      let some ci := env.find? n | throwError "missing {n}"
      let owner := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
      let ty := (← ppExpr ci.type).pretty 1000000000
      let (valHash, used) := match ci with
        | .defnInfo d => (toString d.value.hash, ci.type.getUsedConstants ++ d.value.getUsedConstants)
        | _ => ("-", ci.type.getUsedConstants)
      let ax ← collectAxioms n
      IO.println s!"\n== {n}"
      IO.println s!"owner: {owner}"
      IO.println s!"kind: {kindOf env ci}"
      IO.println s!"levelParams: {ci.levelParams}"
      IO.println s!"type: {ty}"
      IO.println s!"typeHash: {ci.type.hash}"
      IO.println s!"valueHash: {valHash}"
      IO.println s!"usedConstants: {sortNames used}"
      IO.println s!"axioms: {sortNames ax}"
  IO.println "\n== internal"
  for n in internal do
    let some ci := env.find? n | throwError "missing {n}"
    IO.println s!"{n} : {kindOf env ci}"

#eval show MetaM Unit from do
  let some m ← IO.getEnv "INSPECT_MOD" | throwError "set INSPECT_MOD"
  inspect m.toName
