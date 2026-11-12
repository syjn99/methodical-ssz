import Lean

/-!
# inventory_decls: facts about named declarations for `inventory.py` (core `Lean` only)

Usage (`lean` is a heavy command: run it through the heavy-job gate, cwd `fv/kraken/lean`):

    lake env lean --run ../gen/tools/inventory_decls.lean <names.txt> Module...

It imports the given modules. For every name in `<names.txt>` (one per line; blank lines and `#` lines are
skipped) it prints one tab-separated line:

    name  kind  axioms  programs  refs

* `kind`: `theorem`, `def`, … or `MISSING` (then the other columns are `-`).
* `axioms`: the sorted result of `Lean.collectAxioms`, comma separated, `-` if empty.
* `programs`: the constants that occur in the declared TYPE (also inside definitions of type `Prop` that it
  names, e.g. a statement `abbrev`) and whose own type is a constant named `Program`
  (the included machine-code constants, e.g. `E2eScal.H6Code.SaUnmarshal`), sorted, comma separated, `-` if none.
  This is how `inventory.py` keys a theorem to a function of the target: by the code constant in its type,
  not by a file name or a header.
* `refs`: the names of `<names.txt>` that occur in the VALUE of the declaration (for a theorem: its proof term),
  following auxiliary declarations whose name extends the declaration's name (`thm._proof_1`, …), sorted, `-` if
  none. Used to check that a witness or a spec theorem is built on the mapped accept / reject theorem.

The first line is a header with the Lean version and git hash. Exit 0 on success, 2 on a usage error.
-/

open Lean

def kindStr : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "recursor"

def isProgramConst (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some ci => match ci.type with
    | .const n _ => n.getString! == "Program" || n.toString.endsWith ".Program"
    | _ => false
  | none => false

/-- The body of a chain of `∀` / `→` binders (the codomain). -/
def codomain : Expr → Expr
  | .forallE _ _ b _ => codomain b
  | e => e

/-- Constants of a type, following definitions whose type ends in `Prop` (after its binders, e.g. `[Host] → Prop`) (statement abbrevs such as
`E2eScal.H6.pd_accept_stmt`), so that the code constant inside a named statement is found. -/
partial def typeConsts (env : Environment) (t : Expr) : NameSet := Id.run do
  let mut out : NameSet := {}
  let mut todo : List Expr := [t]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let e := todo.head!
    todo := todo.tail!
    for c in e.getUsedConstants do
      out := out.insert c
      if seen.contains c then continue
      seen := seen.insert c
      if let some (.defnInfo d) := env.find? c then
        if (codomain d.type).isProp then todo := d.value :: todo
  return out

/-- Constants used by the value of `n`, following auxiliary declarations `n.*`. -/
partial def valueConsts (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : List Name := [root]
  let mut out : NameSet := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let some v := ci.value? (allowOpaque := true) | continue
    for c in v.getUsedConstants do
      out := out.insert c
      if root.isPrefixOf c && c != root then todo := c :: todo
  return out

def row (env : Environment) (names : List Name) (n : Name) : CoreM String := do
  match env.find? n with
  | none => return s!"{n}\tMISSING\t-\t-\t-"
  | some ci =>
    let axs ← Lean.collectAxioms n
    let axStrs := (axs.map toString).qsort (· < ·)
    let axCol := if axStrs.isEmpty then "-" else ",".intercalate axStrs.toList
    let progs := ((typeConsts env ci.type).toList.filter (isProgramConst env)).toArray.map toString
    let progs := (progs.toList.eraseDups.toArray.qsort (· < ·))
    let pCol := if progs.isEmpty then "-" else ",".intercalate progs.toList
    let vc := valueConsts env n
    let refs := ((names.filter fun m => m != n && vc.contains m).map toString).toArray.qsort (· < ·)
    let rCol := if refs.isEmpty then "-" else ",".intercalate refs.toList
    return s!"{n}\t{kindStr ci}\t{axCol}\t{pCol}\t{rCol}"

def main (args : List String) : IO UInt32 := do
  match args with
  | file :: mods@(_ :: _) =>
    let txt ← IO.FS.readFile file
    let clean := fun (l : String) => String.ofList (l.toList.filter (fun c => c != ' ' && c != '\r' && c != '\t'))
    let names := (txt.splitOn "\n").map clean |>.filter (fun l => !l.isEmpty && !l.startsWith "#")
      |>.map String.toName
    initSearchPath (← findSysroot)
    let env ← importModules (mods.map fun m => ({ module := m.toName } : Import)).toArray {}
    let ctx : Core.Context := { fileName := "<inventory_decls>", fileMap := default }
    let st : Core.State := { env }
    IO.println s!"# inventory_decls v1 lean={Lean.versionString} githash={Lean.githash}"
    for n in names do
      let (r, _) ← (row env names n).toIO ctx st
      IO.println r
    return 0
  | _ =>
    IO.eprintln "usage: lean --run inventory_decls.lean <names.txt> Module..."
    return 2
