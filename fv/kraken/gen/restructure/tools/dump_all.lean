import Lean
open Lean

/-!
Declaration dump for the map builders of the restructuring.
It imports the given modules and writes one line for each constant of the environment:
`module<TAB>name<TAB>kind<TAB>internal`. The internal flag is `1` for a name that `Name.isInternal` accepts.
The dump has the constants of Lean, Std and EthLib too. A map builder selects the rows of the moved modules.

This program is not the declaration dump of the axioms gate. The gate uses
`.claude/skills/maintaining-methodical-fv/scripts/decl_dump.lean`, which writes other columns.

Run it through `dump_all.sh` in this directory. That script gives every module of every `[[lean_lib]]` block of
`fv/kraken/lean/lakefile.toml` as arguments:

    sh fv/kraken/gen/restructure/tools/dump_all.sh <out.tsv>

The script runs `lake env lean --run ../gen/restructure/tools/dump_all.lean <out.tsv> <modules>` in `fv/kraken/lean`.
Run it after `lake build` of every library, under the heavy-job gate.
-/

def kindStr : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "recursor"

def main (args : List String) : IO UInt32 := do
  match args with
  | out :: mods =>
    initSearchPath (← findSysroot)
    let imports := mods.toArray.map fun m => ({ module := m.toName } : Import)
    let env ← importModules imports {} (trustLevel := 1024)
    let h ← IO.FS.Handle.mk out .write
    for (n, ci) in env.constants.toList do
      let modName := match env.getModuleIdxFor? n with
        | some idx => env.header.moduleNames[idx.toNat]!.toString
        | none => "?"
      let internal := if n.isInternal then "1" else "0"
      h.putStrLn s!"{modName}\t{n}\t{kindStr ci}\t{internal}"
    return 0
  | _ => IO.eprintln "usage: dump_all <out> Module..."; return 2
