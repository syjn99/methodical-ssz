module
public import Kraken.X64.Syntax
public meta import Kraken.X64.Parser
public meta import Lean

/-!
`include_x64_rt "file.S"`: elaborate a file with Kraken's runtime parser and
turn the result into a term with the `Lean.ToExpr` instances that Kraken derives
for `Directive`.

Our wrapper, not a Kraken change.
-/

open Lean Elab Term

elab "include_x64_rt" path:str : term => do
  let s ← IO.FS.readFile path.getString
  match Kraken.X64.Parser.parse (Kraken.Parser.stripDirectives s) with
  | .ok p => return toExpr p
  | .error e => throwError "Kraken runtime parser: {e}"
