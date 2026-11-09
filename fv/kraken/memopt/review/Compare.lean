import Lean
open Lean Meta

def constKind (c : ConstantInfo) : String :=
  match c with
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "recursor"

def namesOf (env : Environment) (mods : Array Name) : Array Name := Id.run do
  let mut ns := #[]
  for mod in mods do
    if let some i := env.getModuleIdx? mod then
      ns := ns ++ env.header.moduleData[i.toNat]!.constNames
  return ns.qsort Name.lt

#eval show MetaM Unit from do
  let some dir ← IO.getEnv "REVIEW_DIR" | throwError "REVIEW_DIR missing"
  let mods := #[`Fk.WitLcM0, `Fk.WitLcM1, `Fk.WitLcM4, `Fk.WitLcM1x1,
                `Fk.WitLcM4x16, `Fk.WitLcMMix]
  let base ← searchPathRef.get
  searchPathRef.set (System.FilePath.mk (dir ++ "/orig") :: base)
  for m in mods do IO.println s!"ORIG {m} {(← findOLean m)}"
  let orig ← importModules (mods.map fun m => { module := m }) {} (loadExts := false)
  searchPathRef.set (System.FilePath.mk (dir ++ "/new") :: base)
  for m in mods do IO.println s!"NEW {m} {(← findOLean m)}"
  let fresh ← importModules (mods.map fun m => { module := m }) {} (loadExts := false)
  searchPathRef.set base
  let ns := namesOf orig mods
  unless ns == namesOf fresh mods do throwError "declaration names differ"
  let extra := #[`Fv1.u64Bytes, `EthLib.Serialization.Ssz.uintBytes, `lcElem,
                 `lc_marshal_main, `Int.toBytes]
  let mut defCount := 0
  let mut axChanges := 0
  for n in ns ++ extra do
    let some a := orig.find? n | throwError "missing original {n}"
    let some b := fresh.find? n | throwError "missing new {n}"
    unless constKind a == constKind b do throwError "kind changed {n}"
    unless a.levelParams == b.levelParams do throwError "universe changed {n}"
    unless a.type.equal b.type do throwError "type changed {n}"
    let ownerA := (orig.getModuleIdxFor? n).map (fun i => orig.header.moduleNames[i.toNat]!)
    let ownerB := (fresh.getModuleIdxFor? n).map (fun i => fresh.header.moduleNames[i.toNat]!)
    unless ownerA == ownerB do throwError "owner changed {n}"
    match a, b with
    | .defnInfo da, .defnInfo db =>
        unless da.value.equal db.value do throwError "definition changed {n}"
        defCount := defCount + 1
    | .opaqueInfo da, .opaqueInfo db =>
        unless da.value.equal db.value do throwError "opaque changed {n}"
    | _, _ => pure ()
    setEnv orig
    let aa := (← collectAxioms n).qsort Name.lt
    setEnv fresh
    let ab := (← collectAxioms n).qsort Name.lt
    if aa != ab then
      axChanges := axChanges + 1
      IO.println s!"AXIOMS {n}: {aa} -> {ab}"
      unless (["u64v0", "u64v1", "u64v2", "u64v3"].any (fun s => n.toString.endsWith s)) && aa.isEmpty && ab == (#[`propext, `Quot.sound].qsort Name.lt) do
        throwError "unexpected axiom change {n}"
  unless axChanges == 7 do throwError "expected seven axiom changes, got {axChanges}"
  IO.println s!"PASS: {ns.size} owned declarations, including internal declarations"
  IO.println s!"PASS: {extra.size} external declarations"
  IO.println s!"PASS: {defCount} definition values structurally equal"
  IO.println "PASS: names, owners, kinds, universes and full type expressions equal"
  IO.println "Proof values were not compared. All target modules were compiled separately."
