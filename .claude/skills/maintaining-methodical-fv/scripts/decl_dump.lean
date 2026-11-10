import Lean

/-!
# decl_dump: one stable record per declaration (core `Lean` only)

Usage (`lean` is a heavy command: run it through the heavy-job gate):

    LEAN_PATH=<dir with the .olean files> lean --run decl_dump.lean [--root R]... Module...

It imports the given modules. It prints one tab-separated line per
declaration whose defining module has one of the roots (default: the roots of
the given modules), sorted by name:

    name  kind  type-hash  value-hash  axioms

* `type-hash`: `Expr.hash` of the declared type, printed as 16 hex digits.
* `value-hash`: `Expr.hash` of the value for `def` and `opaque`; `-` for every
  other kind. Theorem proofs are not hashed. A changed proof shows up only if
  it changes the axiom set.
* `axioms`: the sorted result of `Lean.collectAxioms`, comma separated, `-` if
  empty.

The first line is a header with the Lean version and git hash.
`decl_drift.py` refuses to compare dumps from different Lean builds.

Limits: `Expr.hash` is a structural hash; on the tested toolchain only 32 bits
are used (the upper 8 hex digits are 0). It ignores binder names and
binder kind (explicit, implicit, instance-implicit), and it is not a definitional-equivalence check. It is comparable only between dumps
made by the same Lean build. Exit 0 on success, 2 on a usage error or when no
declaration matched.
-/

open Lean

def kindOf : ConstantInfo → String × Option Expr
  | .axiomInfo _  => ("axiom", none)
  | .defnInfo v   => ("def", some v.value)
  | .thmInfo _    => ("theorem", none)
  | .opaqueInfo v => ("opaque", some v.value)
  | .quotInfo _   => ("quot", none)
  | .inductInfo _ => ("inductive", none)
  | .ctorInfo _   => ("ctor", none)
  | .recInfo _    => ("recursor", none)

def hex16 (h : UInt64) : String :=
  let ds := Nat.toDigits 16 h.toNat
  "".pushn '0' (16 - ds.length) ++ String.join (ds.map toString)

def parseArgs : List String → List Name → List Name → Except String (List Name × List Name)
  | [], roots, mods => .ok (roots.reverse, mods.reverse)
  | "--root" :: r :: rest, roots, mods => parseArgs rest (r.toName :: roots) mods
  | "--root" :: [], _, _ => .error "--root needs a value"
  | m :: rest, roots, mods =>
    if m.startsWith "-" then .error s!"unknown option {m}"
    else parseArgs rest roots (m.toName :: mods)

def dumpRows (env : Environment) (roots : List Name) : CoreM (Array String) := do
  let mut rows : Array (String × String) := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless roots.contains mod.getRoot do continue
    let (kind, val) := kindOf ci
    let vh := match val with
      | some v => hex16 v.hash
      | none => "-"
    let axs ← Lean.collectAxioms n
    let axStrs := (axs.map toString).qsort (· < ·)
    let axCol := if axStrs.isEmpty then "-" else ",".intercalate axStrs.toList
    let key := toString n
    rows := rows.push (key, s!"{key}\t{kind}\t{hex16 ci.type.hash}\t{vh}\t{axCol}")
  return (rows.qsort (fun a b => a.1 < b.1)).map (·.2)

def main (args : List String) : IO UInt32 := do
  match parseArgs args [] [] with
  | .error e =>
    IO.eprintln s!"decl_dump: {e}"
    return 2
  | .ok (roots, mods) =>
    if mods.isEmpty then
      IO.eprintln "usage: lean --run decl_dump.lean [--root R]... Module..."
      return 2
    let roots := if roots.isEmpty then mods.map Name.getRoot else roots
    initSearchPath (← findSysroot)
    let env ← importModules (mods.map fun m => ({ module := m } : Import)).toArray {}
    let ctx : Core.Context := { fileName := "<decl_dump>", fileMap := default }
    let st : Core.State := { env }
    let (rows, _) ← (dumpRows env roots).toIO ctx st
    if rows.isEmpty then
      IO.eprintln s!"decl_dump: no declaration under roots {roots}"
      return 2
    IO.println s!"# decl_dump v1 lean={Lean.versionString} githash={Lean.githash} roots={",".intercalate (roots.map toString)}"
    for r in rows do IO.println r
    return 0
