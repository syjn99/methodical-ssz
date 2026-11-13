import Lean
open Lean

/-!
Use count of constants across modules, for the split and removal work of the restructuring.
It imports the given modules. For each constant of a "user" module, it reads the constants that its type and
its value use. It counts the uses of the constants of the "target" modules.

usage (from `fv/kraken/lean`, after `lake build`, under the heavy-job gate):

    lake env lean --run ../gen/restructure/tools/constant_uses.lean <out.tsv> <targets.txt> <users.txt> <Module>...

`targets.txt` and `users.txt` hold one module name per line. Give every module of both lists as `<Module>`.
Each output line is: target constant, its module, number of using constants, one sample user module.
Example: the declarations of one library that other libraries use. Put the modules of that library in `targets.txt` and
the modules of the other libraries in `users.txt`.
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | out :: tf :: uf :: mods =>
    initSearchPath (← findSysroot)
    let tmods := (← IO.FS.lines tf).toList.filter (· ≠ "") |>.map String.toName
    let umods := (← IO.FS.lines uf).toList.filter (· ≠ "") |>.map String.toName
    let imports := mods.toArray.map fun m => ({ module := m.toName } : Import)
    let env ← importModules imports {} (trustLevel := 1024)
    let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => .anonymous
    let mut counts : Std.HashMap Name (Nat × Name) := {}
    for (n, ci) in env.constants.toList do
      let um := modOf n
      if umods.contains um then
        for c in ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[] do
          let tm := modOf c
          if tmods.contains tm then
            let (k, s) := counts.getD c (0, um)
            counts := counts.insert c (k + 1, s)
    let h ← IO.FS.Handle.mk out .write
    for (c, (k, s)) in counts.toList do
      h.putStrLn s!"{c}\t{modOf c}\t{k}\t{s}"
    return 0
  | _ => IO.eprintln "usage: constant_uses <out> <targets.txt> <users.txt> Module..."; return 2
