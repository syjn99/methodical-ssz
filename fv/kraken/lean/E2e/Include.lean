module
public import Kraken.X64.Syntax
public meta import Lean

/-!
# `e2e_data_include id`: ELF data of the Go 1.26.10 namespace (prysm-e2e)

The same reader as `data_include` (`Fk/Include.lean`), for the data directory of
this namespace: `../prysm/go1.26.10/e2e/link/data/<id>.data` (relative to
`fv/kraken/lean`). `Fk/Include.lean` keeps its helpers private to its module
and is not changed; the three helpers below are its text with an `e2e` prefix
on the names (`gen/e2e/check_include.py` compares the bodies). TRUSTED like
`data_include`: this reader. That the file is the ELF's bytes is
`link/check.py`'s data check (f) in `prysm/go1.26.10/e2e/link/RESULT`.
-/

open Lean Elab Term

/-- One byte `hh` (two lowercase hex digits). -/
meta def e2eHexByte? (s : String) : Option Nat :=
  let dig (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  match s.toList with
  | [h, l] => do return 16 * (← dig h) + (← dig l)
  | _ => none

/-- `(label "l" + o).toBitVec`, or `(label "l").toBitVec` for o = 0. -/
meta def e2eLabelTerm (l : String) (o : Nat) : String :=
  if o == 0 then s!"(label \"{l}\").toBitVec" else s!"(label \"{l}\" + {o}).toBitVec"

/-- The Lean source of the two definitions of a data file (see above). -/
meta def e2eDataSource (id text : String) : Except String String := do
  -- one rule with `link/check.py` (f): lines end with `\n`; every other character is
  -- printable ASCII (no `\r`, tab or other control character)
  unless text.toList.all (fun c => c == '\n' || (' ' ≤ c && c ≤ '~')) do
    throw "a character that is not printable ASCII or a newline"
  let mut at? : Option String := none
  let mut parts : Array String := #[]
  let mut raw : Array String := #[]
  let mut host := false
  let mut n := 0
  for line in text.splitOn "\n" do
    match (line.splitOn " ").filter (· ≠ "") with
    | [] => pure ()
    | w :: ws =>
      if w.startsWith "#" then continue
      match w, ws with
      | "at", [l, o] =>
        unless at?.isNone && n == 0 do throw "`at` is not the first directive"
        let some o := o.toNat? | throw s!"bad offset {o}"
        at? := some (e2eLabelTerm l o)
      | "bytes", bs =>
        if at?.isNone then throw "no `at` directive first"
        for b in bs do
          let some v := e2eHexByte? b | throw s!"bad byte {b}"
          raw := raw.push (toString v); n := n + 1
      | "word", [l, o] =>
        if at?.isNone then throw "no `at` directive first"
        let some o := o.toNat? | throw s!"bad offset {o}"
        unless raw.isEmpty do parts := parts.push s!"[{", ".intercalate raw.toList}]"
        raw := #[]
        parts := parts.push s!"Int.toBytes 8 {e2eLabelTerm l o}.toInt"
        host := true; n := n + 8
      | _, _ => throw s!"bad directive: {line}"
  unless raw.isEmpty do parts := parts.push s!"[{", ".intercalate raw.toList}]"
  let some a := at? | throw "no `at` directive"
  let addr := s!"def {id}_addr [Host] : BitVec 64 := {a}\n"
  if parts.isEmpty then return addr
  let hb := if host then " [Host]" else ""
  return addr ++ s!"def {id}{hb} : List UInt8 := {" ++ ".intercalate parts.toList}\n"

open Lean Elab Command in
elab "e2e_data_include " id:ident : command => do
  let n := id.getId.toString
  let text ← IO.FS.readFile s!"../prysm/go1.26.10/e2e/link/data/{n}.data"
  match e2eDataSource n text with
  | .error e => throwError "e2e_data_include {n}: {e}"
  | .ok src =>
    for cmd in src.splitOn "\n" do
      if cmd.isEmpty then continue
      match Parser.runParserCategory (← getEnv) `command cmd with
      | .ok stx => elabCommand stx
      | .error e => throwError "e2e_data_include {n}: {e}"
