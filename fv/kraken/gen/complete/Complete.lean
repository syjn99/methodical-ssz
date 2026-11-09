import Fk

/-!
# Dependency-based completion data (phase1c P5)

Reads resolved declarations only (no source text). Input: `$COMPLETE_MAINS`, a
file with one fully qualified theorem name per line (the main theorems of the
frozen list `gen/frozen/THEOREMS.json`, plus the composition theorems).
For each name it prints one `COMPLETE <json>` line:

* `module`        module of the declaration
* `witnesses`     declarations of `Fk` modules whose proof term uses the theorem,
                  whose type has no binder of type `Host`, and which use a concrete
                  `Host` instance; with the instances they use
* `users`         other `Fk` declarations that use the theorem (with a `Host` binder)
* `ethlib_links`  users whose type mentions `EthLib…deserialize` or `serialize`
* `contracts`     registry contracts in the theorem's hypotheses (resolved
                  constants); `contracts_via` adds, for every function-spec
                  contract, the contracts of the declarations that conclude it
* `post`          flags of the conclusion `Eventually _ (fun st => P) _`:
                  `dmem_eq` (an `Eq` on `DataMem`), `frame` (a hypothesis of type
                  `DataMem → Prop` occurs in P), `true` (`True` occurs in P)
* `data_consts`   hand constants the include API replaces (resolved names)
* `COMPLETE-MAINS` line: the `*_main` theorems of the `Fk` modules (enumerated from the
                  environment) against the `*_main` names of the input; any difference is an error
* `dependent_mains` input names whose proof term reaches this one through Fk
                  constants (auxiliary declarations included)

Run (gated): `cd fv/kraken/lean && COMPLETE_MAINS=<file> lake env lean ../gen/complete/Complete.lean`
-/

open Lean Meta
open Fk Fk.Code Fv1 EthLib.Serialization.Ssz

namespace Complete

-- Double-backtick names are resolved when this file elaborates: a name that does
-- not exist is an elaboration error, not a silent miss.
def registry : List Name :=
  [``MakesliceC, ``MemmoveC, ``GrowsliceC, ``NewobjectC, ``ConvT64C, ``FmtErrorfNilC,
   ``FmtErrorfWC, ``FmtErrorfDWC, ``ValidateBitlistC, ``ValidateBitlistErrC,
   ``VbvAccC, ``VbvPadC, ``ScUAccC, ``LuUAccC]

def funSpecs : List Name := [``VbvAccC, ``VbvPadC, ``ScUAccC, ``LuUAccC]

def dataConsts : List Name :=
  [``blFmtB, ``bvFmtJ, ``vbvFmt, ``lcFmtZero, ``lcFmtShort, ``vblMsgE, ``vblMsgZ, ``vblMsgB,
   ``luFmtTooBig, ``luFmtMis, ``luTW, ``StaticBox]

def ethlibCodec : List Name := [``EthLib.Serialization.Ssz.deserialize, ``EthLib.Serialization.Ssz.serialize]

def inFk (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).getRoot == `Fk
  | none => false

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => toString env.header.moduleNames[i.toNat]!
  | none => "?"

-- Telescopes do not reduce: a contract such as `ScUAccC` is a `def : Prop` and must
-- stay visible as the head of a conclusion or hypothesis.
-- `value? (allowOpaque := true)` is needed to read theorem proof terms.

/-- Does the type have a binder whose type is the class `Host`? -/
def hasHostBinder (t : Expr) : MetaM Bool :=
  forallTelescope t fun xs _ => xs.anyM fun x => do
    let ty ← inferType x
    return ty.isConstOf ``Host

def hostConsts (env : Environment) (e : Expr) : MetaM (List Name) := do
  let mut out := []
  for c in e.getUsedConstants do
    if inFk env c then
      if let some ci := env.find? c then
        if ci.type.isConstOf ``Host then out := out ++ [c]
  return out

def hypContracts (t : Expr) : MetaM (List Name) :=
  forallTelescope t fun xs _ => do
    let mut out : List Name := []
    for x in xs do
      let ty ← inferType x
      for c in ty.getUsedConstants do
        if registry.contains c && !out.contains c then out := out ++ [c]
    return out

def concludes (t : Expr) (c : Name) : MetaM Bool :=
  forallTelescope t fun _ b => return b.getAppFn.isConstOf c

def postFlags (t : Expr) : MetaM (Bool × Bool × Bool × Bool) :=
  forallTelescope t fun xs b => do
    if !b.getAppFn.isConstOf ``Eventually then return (false, false, false, false)
    let args := b.getAppArgs
    let p := args[args.size - 2]!
    let frames ← xs.filterM fun x => do
      let ty ← inferType x
      return ty.isArrow && (ty.bindingDomain!.isConstOf ``DataMem) && ty.bindingBody!.isProp
    let hasFrame := frames.any fun f => (p.find? (· == f)).isSome
    let hasTrue := (p.find? (·.isConstOf ``True)).isSome
    let eqMem := (p.find? fun e => e.isAppOfArity ``Eq 3 && (e.getArg! 0).isConstOf ``DataMem).isSome
    return (true, eqMem, hasFrame, hasTrue)

def jsonNames (ns : List Name) : Json := Json.arr (ns.map (fun n => Json.str (toString n))).toArray

def main : MetaM Unit := do
  let env ← getEnv
  let some path ← IO.getEnv "COMPLETE_MAINS" | throwError "COMPLETE_MAINS is not set"
  let mains := ((← IO.FS.readFile path).splitOn "\n").filter (· ≠ "") |>.map String.toName
  -- resolve the registry first: every name must exist
  for c in registry ++ dataConsts do
    if !env.contains c then throwError "registry name does not resolve: {c}"
  -- one pass over Fk declarations: used constants of values and types
  let mut uses : Std.HashMap Name (Array Name) := {}
  let mut graph : Std.HashMap Name (Array Name) := {}  -- Fk decl -> Fk constants its value uses
  let mut fkDecls : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if !inFk env n then continue
    let vs := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]
    graph := graph.insert n (vs.filter (inFk env))
    if n.isInternal then continue
    fkDecls := fkDecls.push n
    for c in vs do
      if mains.contains c then
        uses := uses.insert c ((uses.getD c #[]).push n)
  -- mains whose proof term reaches `target` through Fk constants (auxiliary declarations included)
  let reaches (start target : Name) : Bool := Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut stack := #[start]
    let mut found := false
    while !stack.isEmpty && !found do
      let x := stack.back!
      stack := stack.pop
      if seen.contains x then continue
      seen := seen.insert x
      for y in graph.getD x #[] do
        if y == target then found := true
        else if !seen.contains y then stack := stack.push y
    return found
  -- cross-check: the `*_main` theorems of the Fk modules = the `*_main` names of the input
  let envMains := fkDecls.filter (fun n => match env.find? n with
    | some (.thmInfo _) => (n.componentsRev.head?.map (·.toString.endsWith "_main")).getD false
    | _ => false)
  let inMains := mains.filter (fun n => (n.componentsRev.head?.map (·.toString.endsWith "_main")).getD false)
  let missing := envMains.toList.filter (fun n => !inMains.contains n)
  let extra := inMains.filter (fun n => !envMains.contains n)
  IO.println s!"COMPLETE-MAINS env {envMains.size} input {inMains.length} missing_from_input {missing} not_in_env {extra}"
  if !missing.isEmpty || !extra.isEmpty then
    throwError "the input list of *_main theorems differs from the environment"
  -- holders of function specs
  let mut holders : List (Name × Name × List Name) := []
  for n in fkDecls do
    let ci := env.find? n |>.get!
    for s in funSpecs do
      if ← concludes ci.type s then
        holders := holders ++ [(s, n, ← hypContracts ci.type)]
  for m in mains do
    let some ci := env.find? m | IO.println s!"COMPLETE {Json.compress (Json.mkObj [("name", toString m), ("error", "does not resolve")])}"; continue
    let us := (uses.getD m #[]).toList
    let mut wits : List Json := []
    let mut users : List Name := []
    let mut links : List Name := []
    for u in us do
      let uci := env.find? u |>.get!
      if ← hasHostBinder uci.type then
        users := users ++ [u]
        let tc := uci.type.getUsedConstants
        if tc.any ethlibCodec.contains then
          links := links ++ [u]
      else
        let hs ← hostConsts env (uci.type.headBeta)
        let hs2 ← hostConsts env ((uci.value? (allowOpaque := true)).getD (mkConst ``True))
        -- a witness fixes a concrete Host instance; a declaration with neither a Host
        -- binder nor a Host instance (a spec-level lemma) is a user, not a witness
        if (hs ++ hs2).isEmpty then
          users := users ++ [u]
        else
          wits := wits ++ [Json.mkObj [("name", toString u), ("module", moduleOf env u), ("hosts", jsonNames (hs ++ hs2).eraseDups)]]
    let direct ← hypContracts ci.type
    let mut via : List Json := []
    for c in direct do
      if funSpecs.contains c then
        for (s, h, cs) in holders do
          if s == c then via := via ++ [Json.mkObj [("spec", toString s), ("holder", toString h), ("contracts", jsonNames cs)]]
    let dependents := mains.filter (fun x => x != m && reaches x m)
    let (isEv, eqMem, frame, tru) ← postFlags ci.type
    let dcs := ci.type.getUsedConstants.toList.filter dataConsts.contains
    let j := Json.mkObj [("name", toString m), ("module", moduleOf env m), ("witnesses", Json.arr wits.toArray),
      ("users", jsonNames users), ("ethlib_links", jsonNames links), ("contracts", jsonNames direct),
      ("contracts_via", Json.arr via.toArray),
      ("post", Json.mkObj [("eventually", isEv), ("dmem_eq", eqMem), ("frame", frame), ("true", tru)]),
      ("data_consts", jsonNames dcs), ("dependent_mains", jsonNames dependents)]
    IO.println s!"COMPLETE {j.compress}"
  IO.println s!"COMPLETE-DONE {mains.length} {fkDecls.size}"

end Complete

#eval Complete.main
