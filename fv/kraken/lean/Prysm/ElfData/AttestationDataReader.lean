module
public import Kraken.X64.Syntax
public meta import Lean

/-!
# `ad_data_include id`: ELF data of the AttestationData set (prysm-e2e A1)

The same reader as `e2e_data_include` (`Prysm/ElfData/CheckpointAndEpochReader.lean`, itself the text of
`Machine/Include.lean`'s `data_include`), for the data directory
`../prysm/go1.26.10/e2e/ad/link/data/<id>.data` (relative to `fv/kraken/lean`).
`Prysm/ElfData/CheckpointAndEpochReader.lean` keeps its helpers private to its module and is not changed;
the helpers below are its text with the `e2e` prefix replaced by `ad`
(`gen/e2e/check_include.py` compares the bodies). TRUSTED like `data_include`:
this reader. That the files are the ELF's bytes is `link/check.py`'s data check
(f) in `prysm/go1.26.10/e2e/ad/link/RESULT`.
-/

open Lean Elab Term

/-- One byte `hh` (two lowercase hex digits). -/
meta def adHexByte? (s : String) : Option Nat :=
  let dig (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  match s.toList with
  | [h, l] => do return 16 * (← dig h) + (← dig l)
  | _ => none

/-- `(label "l" + o).toBitVec`, or `(label "l").toBitVec` for o = 0. -/
meta def adLabelTerm (l : String) (o : Nat) : String :=
  if o == 0 then s!"(label \"{l}\").toBitVec" else s!"(label \"{l}\" + {o}).toBitVec"

/-- The Lean source of the two definitions of a data file (see above). -/
meta def adDataSource (id text : String) : Except String String := do
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
        at? := some (adLabelTerm l o)
      | "bytes", bs =>
        if at?.isNone then throw "no `at` directive first"
        for b in bs do
          let some v := adHexByte? b | throw s!"bad byte {b}"
          raw := raw.push (toString v); n := n + 1
      | "word", [l, o] =>
        if at?.isNone then throw "no `at` directive first"
        let some o := o.toNat? | throw s!"bad offset {o}"
        unless raw.isEmpty do parts := parts.push s!"[{", ".intercalate raw.toList}]"
        raw := #[]
        parts := parts.push s!"Int.toBytes 8 {adLabelTerm l o}.toInt"
        host := true; n := n + 8
      | _, _ => throw s!"bad directive: {line}"
  unless raw.isEmpty do parts := parts.push s!"[{", ".intercalate raw.toList}]"
  let some a := at? | throw "no `at` directive"
  let addr := s!"def {id}_addr [Host] : BitVec 64 := {a}\n"
  if parts.isEmpty then return addr
  let hb := if host then " [Host]" else ""
  return addr ++ s!"def {id}{hb} : List UInt8 := {" ++ ".intercalate parts.toList}\n"

open Lean Elab Command in
elab "ad_data_include " id:ident : command => do
  let n := id.getId.toString
  let text ← IO.FS.readFile s!"../prysm/go1.26.10/e2e/ad/link/data/{n}.data"
  match adDataSource n text with
  | .error e => throwError "ad_data_include {n}: {e}"
  | .ok src =>
    for cmd in src.splitOn "\n" do
      if cmd.isEmpty then continue
      match Parser.runParserCategory (← getEnv) `command cmd with
      | .ok stx => elabCommand stx
      | .error e => throwError "ad_data_include {n}: {e}"
