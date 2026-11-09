import Lean.Data.Json
import EthLib.Serialization.Ssz
import Fv1.SpecScalars
import Fv1.SpecList
import Fv1.SpecFixedVec
import Fv1.SpecBitVec
import Fv1.SpecNested
import Fv1.SpecListC
import Fv1.SpecPrysm
import Fv1.SpecBitList

/-!
# Independent `Desc` checker (phase1c P3)

Reads producer `Desc` JSON files (schema `fvphase1c.desc/1`, listed one path per
line in `$DESC_LIST`) and compares every claim with the pinned EthLib SSZ spec:

* `parse`      the `ssz` term is an EthLib `Desc` (container at top level)
* `wf`         `Desc.wellFormed = .ok ()`
* `fixed`      claimed `fixed_size` = `Desc.fixedSize`
* `nfields`    one claim per EthLib field
* `width`, `variable`, `offset`, `kind`, `length`, `limit`, `elem`
               per field, from EthLib `Desc.fixedSize` of the field (variable
               fields take `bytesPerOffset` head bytes) and the field's
               constructor arguments; offsets are prefix sums of the widths
* `head`       claimed `fixed_part_size` = sum of the head widths
* `order`      claimed `variable_order` = the variable fields in field order
* `ref`        if `reference` names a hand-written EthLib `Desc` (Fv1), the
               shape equals it up to field names (EthLib `Desc.beq` after
               positional renaming)
* `probe`      EthLib `serialize` of `Desc.default`: total size = head + the
               default body of each variable field; each variable field's head
               offset word at its claimed offset; for each fixed field, a marker value
               changes bytes only inside [offset, offset + width). Skipped when
               the head is larger than 65536 bytes.

Prints `DESCCHECK <file> <check> OK|FAIL|SKIP <detail>` per check and
`DESCCHECK-FILE <file> PASS|FAIL <failed checks>` per file, then
`DESCCHECK-DONE <pass> <fail>`. Shares no code with the producer
(`gen/desc/producer.py`). Read-only; adds no declaration used elsewhere.

Run (gated): `cd fv/kraken/lean && DESC_LIST=<file> lake env lean ../gen/desccheck/DescCheck.lean`
-/

open Lean EthLib.Serialization.Ssz

namespace DescCheck

partial def toDesc (j : Json) : Except String Desc := do
  let k ← j.getObjValAs? String "k"
  match k with
  | "bool" => pure .bool
  | "uint" => return .uint (← j.getObjValAs? Nat "w")
  | "byteVector" => return .byteVector (← j.getObjValAs? Nat "n")
  | "byteList" => return .byteList (← j.getObjValAs? Nat "limit")
  | "bitVector" => return .bitVector (← j.getObjValAs? Nat "n")
  | "bitList" => return .bitList (← j.getObjValAs? Nat "limit")
  | "vector" => return .vector (← toDesc (← j.getObjVal? "elem")) (← j.getObjValAs? Nat "n")
  | "list" => return .list (← toDesc (← j.getObjVal? "elem")) (← j.getObjValAs? Nat "limit")
  | "container" =>
    let names ← j.getObjValAs? (List String) "names"
    let fs ← (← j.getObjValAs? (Array Json) "fields").toList.mapM toDesc
    if names.length != fs.length then throw "names and fields differ in length"
    return .container names fs
  | other => throw s!"unknown kind {other}"

partial def posNames : Desc → Desc
  | .vector e n => .vector (posNames e) n
  | .list e n => .list (posNames e) n
  | .container ns fs => .container ((List.range ns.length).map toString) (fs.map posNames)
  | d => d

def kindName : Desc → String
  | .bool => "bool" | .uint _ => "uint" | .byteVector _ => "byteVector" | .byteList _ => "byteList"
  | .bitVector _ => "bitVector" | .bitList _ => "bitList" | .vector _ _ => "vector" | .list _ _ => "list"
  | .container _ _ => "container" | _ => "other"

def refs : List (String × Desc) :=
  [("Fv1.scDesc", Fv1.scDesc), ("Fv1.fvDesc", Fv1.fvDesc), ("Fv1.luDesc", Fv1.luDesc),
   ("Fv1.bvDesc", Fv1.bvDesc), ("Fv1.neDesc", Fv1.neDesc), ("Fv1.lcDesc", Fv1.lcDesc),
   ("Fv1.blDesc", Fv1.blDesc), ("Fv1.cpDesc", Fv1.cpDesc), ("Fv1.adDesc", Fv1.adDesc)]

/-- A value of a fixed-size shape with every byte or bit set. -/
partial def marker : Desc → Option Value
  | .bool => some (.bool true)
  | .uint w => some (.uint (2 ^ (8 * w) - 1))
  | .byteVector n => some (.bytes (Array.replicate n 0xff))
  | .bitVector n => some (.bits (Array.replicate n true))
  | .vector e n => do let m ← marker e; some (.seq (List.replicate n m))
  | .container _ fs => do let ms ← fs.mapM marker; some (.seq ms)
  | _ => none

def le32 (bs : Array UInt8) (o : Nat) : Nat :=
  (List.range 4).foldl (fun acc i => acc + (bs[o + i]!).toNat * 256 ^ i) 0

abbrev Line := String × Bool × String  -- check, ok, detail

def optNat (j : Json) (k : String) : Except String (Option Nat) :=
  match j.getObjVal? k with
  | .ok .null => .ok none
  | .ok v => (fromJson? v : Except String Nat).map some
  | .error _ => .ok none

def checkFields (j : Json) (fs : List Desc) : Except String (List Line × Nat × List Nat) := do
  let claims ← j.getObjValAs? (Array Json) "fields"
  let mut out : List Line := []
  if claims.size != fs.length then
    out := out ++ [("nfields", false, s!"claimed {claims.size}, EthLib {fs.length}")]
  else
    out := out ++ [("nfields", true, s!"{fs.length}")]
  let mut off := 0
  let mut vars : List Nat := []
  for i in [0:fs.length] do
    let f := fs[i]!
    let w := f.fixedSize.getD bytesPerOffset
    let isVar := f.fixedSize.isNone
    if isVar then vars := vars ++ [i]
    if h : i < claims.size then
      let c := claims[i]
      let cw ← c.getObjValAs? Nat "width"
      let cv ← c.getObjValAs? Bool "variable"
      let co ← c.getObjValAs? Nat "offset"
      let ck ← c.getObjValAs? String "kind"
      out := out ++ [(s!"width[{i}]", cw == w, s!"claimed {cw}, EthLib {w}"),
                     (s!"variable[{i}]", cv == isVar, s!"claimed {cv}, EthLib {isVar}"),
                     (s!"offset[{i}]", co == off, s!"claimed {co}, EthLib {off}"),
                     (s!"kind[{i}]", ck == kindName f, s!"claimed {ck}, EthLib {kindName f}")]
      match f with
      | .byteVector n | .bitVector n =>
        let cl ← optNat c "length"
        out := out ++ [(s!"length[{i}]", cl == some n, s!"claimed {cl}, EthLib {n}")]
      | .vector e n =>
        let cl ← optNat c "length"
        let ce ← optNat c "elem_size"
        out := out ++ [(s!"length[{i}]", cl == some n, s!"claimed {cl}, EthLib {n}"),
                       (s!"elem[{i}]", ce == e.fixedSize, s!"claimed {ce}, EthLib {e.fixedSize}")]
      | .byteList l | .bitList l =>
        let cl ← optNat c "limit"
        out := out ++ [(s!"limit[{i}]", cl == some l, s!"claimed {cl}, EthLib {l}")]
      | .list e l =>
        let cl ← optNat c "limit"
        let ce ← optNat c "elem_size"
        out := out ++ [(s!"limit[{i}]", cl == some l, s!"claimed {cl}, EthLib {l}"),
                       (s!"elem[{i}]", ce == e.fixedSize, s!"claimed {ce}, EthLib {e.fixedSize}")]
      | _ => pure ()
    off := off + w
  return (out, off, vars)

def probe (d : Desc) (fs : List Desc) (head : Nat) (fixed : Option Nat) (claims : Array Json) :
    Except String (List Line) := do
  let v ← (d.default).mapError (fun e => s!"default: {repr e}")
  let bs ← (serialize d v).mapError (fun e => s!"serialize: {repr e}")
  let vals ← match v with
    | .seq xs => pure xs
    | _ => throw "default is not a sequence"
  -- body length of each field's default value (0 for fixed fields), from EthLib serialize
  let mut bodies : List Nat := []
  for i in [0:fs.length] do
    let f := fs[i]!
    if f.fixedSize.isNone then
      let fb ← (serialize f (vals.getD i default)).mapError (fun e => s!"serialize field {i}: {repr e}")
      bodies := bodies ++ [fb.size]
    else
      bodies := bodies ++ [0]
  let total := fixed.getD (head + bodies.foldl (· + ·) 0)
  let mut out : List Line := [("probe-size", bs.size == total, s!"serialized {bs.size}, claimed head {head} + default bodies = {total}")]
  for i in [0:fs.length] do
    if h : i < claims.size then
      let c := claims[i]
      let co ← c.getObjValAs? Nat "offset"
      let cw ← c.getObjValAs? Nat "width"
      let f := fs[i]!
      if f.fixedSize.isNone then
        let want := head + ((bodies.take i).foldl (· + ·) 0)
        let ok := co + 4 ≤ bs.size && le32 bs co == want
        out := out ++ [(s!"probe-var[{i}]", ok, s!"offset word at {co} = {if co + 4 ≤ bs.size then le32 bs co else 0}, expected {want}")]
      else
        match marker f with
        | none => out := out ++ [(s!"probe-fix[{i}]", false, "no marker")]
        | some m =>
          let bs2 ← (serialize d (.seq (vals.set i m))).mapError (fun e => s!"serialize marked: {repr e}")
          let diffs := (List.range (min bs.size bs2.size)).filter (fun p => bs[p]! != bs2[p]!)
          let ok := bs2.size == bs.size && !diffs.isEmpty && diffs.all (fun p => co ≤ p && p < co + cw)
          out := out ++ [(s!"probe-fix[{i}]", ok,
            s!"changed bytes {diffs.head?.getD 0}..{diffs.getLast?.getD 0} ({diffs.length}), claimed [{co},{co + cw})")]
  return out

def checkFile (path : String) : IO (List Line) := do
  let txt ← IO.FS.readFile path
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => return [("json", false, e)]
  let d ← match (j.getObjVal? "ssz") >>= toDesc with
    | .ok d => pure d
    | .error e => return [("parse", false, e)]
  let fs ← match d with
    | .container _ fs => pure fs
    | _ => return [("parse", false, "top level is not a container")]
  let mut out : List Line := [("parse", true, "")]
  out := out ++ [("wf", (match d.wellFormed with | .ok _ => true | .error _ => false),
                  (match d.wellFormed with | .ok _ => "" | .error e => s!"{repr e}"))]
  let cf := optNat j "fixed_size"
  match cf with
  | .ok c => out := out ++ [("fixed", c == d.fixedSize, s!"claimed {c}, EthLib {d.fixedSize}")]
  | .error e => out := out ++ [("fixed", false, e)]
  match checkFields j fs with
  | .error e => out := out ++ [("fields", false, e)]
  | .ok (ls, head, vars) =>
    out := out ++ ls
    match j.getObjValAs? Nat "fixed_part_size" with
    | .ok h => out := out ++ [("head", h == head, s!"claimed {h}, EthLib {head}")]
    | .error e => out := out ++ [("head", false, e)]
    match j.getObjValAs? (List Nat) "variable_order" with
    | .ok o => out := out ++ [("order", o == vars, s!"claimed {o}, EthLib {vars}")]
    | .error e => out := out ++ [("order", false, e)]
    if head > 65536 then
      out := out ++ [("probe", true, s!"SKIP head {head} > 65536")]
    else
      match j.getObjValAs? (Array Json) "fields" with
      | .error e => out := out ++ [("probe", false, e)]
      | .ok claims =>
        match probe d fs head d.fixedSize claims with
        | .ok ls => out := out ++ ls
        | .error e => out := out ++ [("probe", false, e)]
  match j.getObjVal? "reference" with
  | .ok (.str r) =>
    match refs.lookup r with
    | some rd => out := out ++ [("ref", Desc.beq (posNames d) (posNames rd), s!"reference {r}")]
    | none => out := out ++ [("ref", false, s!"unknown reference {r}")]
  | _ => pure ()
  return out

def main : IO Unit := do
  let some list ← IO.getEnv "DESC_LIST" | throw (IO.userError "DESC_LIST is not set")
  let paths := (← IO.FS.readFile list).splitOn "\n" |>.filter (· ≠ "")
  let mut pass := 0
  let mut fail := 0
  for p in paths do
    let ls ← checkFile p
    for (c, ok, det) in ls do
      let st := if det.startsWith "SKIP" then "SKIP" else if ok then "OK" else "FAIL"
      IO.println s!"DESCCHECK {p} {c} {st} {det}"
    let bad := ls.filter (fun l => !l.2.1) |>.map (·.1)
    if bad.isEmpty then
      pass := pass + 1
      IO.println s!"DESCCHECK-FILE {p} PASS"
    else
      fail := fail + 1
      IO.println s!"DESCCHECK-FILE {p} FAIL {String.intercalate "," bad}"
  IO.println s!"DESCCHECK-DONE {pass} {fail}"

end DescCheck

#eval DescCheck.main
