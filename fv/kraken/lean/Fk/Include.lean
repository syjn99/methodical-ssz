module
public import Kraken.X64.Syntax
public meta import Kraken.X64.Parser
public meta import Lean

/-!
`include_x64_rt "file.S"`: elaborate a file with Kraken's runtime parser
(`Kraken.X64.Parser.parse`) and turn the result into a term with the
`Lean.ToExpr` instances that Kraken derives for `Directive`.

Our wrapper, not a Kraken change. Reason: Kraken's `include_x64` elaborator
rejects `jg`/`jge` (its `cc` affix set lacks g, ge, nl, nle, s, ns, o, no, p, np),
while the runtime parser and the semantics (`CondCode`) have them.
`Fk/Code.lean` checks by `rfl` that both parsers give the same term on the
functions that `include_x64` accepts.
-/

open Lean Elab Term

elab "include_x64_rt" path:str : term => do
  let s ← IO.FS.readFile path.getString
  match Kraken.X64.Parser.parse (Kraken.Parser.stripDirectives s) with
  | .ok p => return toExpr p
  | .error e => throwError "Kraken runtime parser: {e}"
