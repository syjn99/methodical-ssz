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

Reads producer `Desc` JSON files (schema `fvphase1c.desc/1`): the originals, one path
per line in `$DESC_LIST`, and optionally negative cases in `$DESC_MUTANTS`. It checks
every claim with the functions of the pinned EthLib SSZ library. Only `ref` and
`go-names` compare with a spec Desc, and only for the types of the checker's own
table (status SPEC); for every other type (status NONE) the checks are consistency
with EthLib layout semantics, not a spec comparison.

Identity (checker rules; the file's values never select what is checked):
* `schema`     exactly `fvphase1c.desc/1`
* `type`       non-empty ASCII identifier (letters, digits, `_`): no look-alike characters
* `package`    one of the checker-owned `knownPackages`
* `table-type` a table type name under another hand package is a FAIL. (Prysm packages
               have real types of the same names, e.g. `Checkpoint`; those are
               told apart by the coverage rule below.)
* `keys`       no unknown key at the top level, in a claim, or in a term

Per file:
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
* `name`, `index` per field: the claim's `name` is the term's field name, `index` = i
* `ref-claim`  a type in the table must carry exactly the table's `reference`; a type
               not in the table must carry none
* `ref`        table type: the shape equals the Fv1 spec Desc up to field names
* `go-names`   table type: the term equals, exactly and with names at every level,
               the checker's Go-named term (Fv1 term with the checker's 21 Go field
               names). So reordered or renamed fields of equal shape FAIL.
* `probe`      EthLib `serialize` of `Desc.default`: total size = head + the
               default body of each variable field; each variable field's head
               offset word at its claimed offset; for each fixed field, a marker value
               changes bytes only inside [offset, offset + width). Skipped when
               the head is larger than 65536 bytes.

Over the originals (`$DESC_LIST`): every key of the table must appear exactly once as
PASS SPEC (`DESCCHECK-COVERAGE`), and no (package, type) key may appear twice
(`DESCCHECK-DUPKEY`). The expected set comes from the checker's table. A table
self-check requires the Go-named terms to equal the Fv1 terms up to names (21 names).
If the self-check, the coverage or any original fails, the run ends with an error
(non-zero exit) after printing `DESCCHECK-TABLE FAIL`.

Prints `DESCCHECK <file> <check> OK|FAIL|SKIP <detail>` per check,
`DESCCHECK-FILE <file> PASS|FAIL SPEC|NONE original|mutant fnv=<FNV-1a 64> <failed checks>`
per file, `DESCCHECK-DONE originals ...` and `DESCCHECK-DONE mutants ...` (counted
apart), then `DESCCHECK-TABLE OK|FAIL`. Shares no code with the producer
(`gen/desc/producer.py`). Read-only; adds no declaration used elsewhere.

Run (gated): `cd fv/kraken/lean && DESC_LIST=<file> [DESC_MUTANTS=<file>] lake env lean ../gen/desccheck/DescCheck.lean`
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

def tgt : String := "github.com/OffchainLabs/methodical-ssz/fv/kraken/target"
def tgtPrysm : String := "github.com/OffchainLabs/methodical-ssz/fv/kraken/target/prysm"

def prysmV1 : String := "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
def prysmEngine : String := "github.com/OffchainLabs/prysm/v7/proto/engine/v1"

/-- Checker-owned package list. Any other `package` value is a FAIL. -/
def knownPackages : List String := [tgt, tgtPrysm, prysmV1, prysmEngine]

/-- Replace the top-level field names of a container term. -/
def rn (ns : List String) : Desc → Desc
  | .container _ fs => .container ns fs
  | d => d

/-! Checker-owned Go field names of the 9 hand types (21 names). The Go-named terms
are the Fv1 spec terms with the Go field names at every container level; a self-check
in `main` requires them to equal the Fv1 terms up to names. -/
def scGo : Desc := rn ["A", "B", "C", "D", "E"] Fv1.scDesc
def luGo : Desc := rn ["L"] Fv1.luDesc
def fvGo : Desc := rn ["R", "W"] Fv1.fvDesc
def bvGo : Desc := rn ["J"] Fv1.bvDesc
def blGo : Desc := rn ["B"] Fv1.blDesc
def cpGo : Desc := rn ["Epoch", "Root"] Fv1.cpDesc
def neGo : Desc := match Fv1.neDesc with
  | .container _ [a, _, _] => .container ["A", "S", "L"] [a, scGo, luGo]
  | d => d
def lcGo : Desc := match Fv1.lcDesc with
  | .container _ [.list _ n] => .container ["Items"] [.list luGo n]
  | d => d
def adGo : Desc := match Fv1.adDesc with
  | .container _ [a, b, c, _, _] =>
    .container ["Slot", "CommitteeIndex", "BeaconBlockRoot", "Source", "Target"] [a, b, c, cpGo, cpGo]
  | d => d

/-- Checker-owned spec table: (package, type) -> (reference name, Fv1 spec Desc, Go-named Desc). -/
def refs : List ((String × String) × (String × Desc × Desc)) :=
  [((tgt, "Scalars"), ("Fv1.scDesc", Fv1.scDesc, scGo)), ((tgt, "FixedVec"), ("Fv1.fvDesc", Fv1.fvDesc, fvGo)),
   ((tgt, "ListU64"), ("Fv1.luDesc", Fv1.luDesc, luGo)), ((tgt, "BitVec"), ("Fv1.bvDesc", Fv1.bvDesc, bvGo)),
   ((tgt, "Nested"), ("Fv1.neDesc", Fv1.neDesc, neGo)), ((tgt, "ListC"), ("Fv1.lcDesc", Fv1.lcDesc, lcGo)),
   ((tgt, "BitL"), ("Fv1.blDesc", Fv1.blDesc, blGo)), ((tgtPrysm, "Checkpoint"), ("Fv1.cpDesc", Fv1.cpDesc, cpGo)),
   ((tgtPrysm, "AttestationData"), ("Fv1.adDesc", Fv1.adDesc, adGo))]

def handPackages : List String := [tgt, tgtPrysm]
def handTypeNames : List String := refs.map (·.1.2)

/-- A Go type name: non-empty, ASCII letters, digits and `_` only (no look-alike characters). -/
def goIdent (s : String) : Bool := !s.isEmpty && s.all (fun c => c.isAlphanum || c == '_')

def topKeys : List String :=
  ["schema", "type", "package", "ssz", "fixed_size", "fixed_part_size", "fields", "variable_order", "reference"]
def claimKeys : List String :=
  ["name", "index", "offset", "width", "variable", "kind", "length", "limit", "elem_size"]

def keysOf : Json → List String
  | .obj kvs => kvs.toList.map Prod.fst
  | _ => []

/-- Keys of a term object that its kind allows. -/
def termKeys : String → List String
  | "bool" => ["k"] | "uint" => ["k", "w"] | "byteVector" => ["k", "n"] | "bitVector" => ["k", "n"]
  | "byteList" => ["k", "limit"] | "bitList" => ["k", "limit"] | "vector" => ["k", "elem", "n"]
  | "list" => ["k", "elem", "limit"] | "container" => ["k", "names", "fields"] | _ => []

/-- Unknown keys anywhere in a term, as paths. -/
partial def termUnknown (path : String) (j : Json) : List String :=
  let k := (j.getObjValAs? String "k").toOption.getD ""
  let own := (keysOf j).filter (fun x => !(termKeys k).contains x) |>.map (fun x => s!"{path}.{x}")
  let sub := match k with
    | "vector" | "list" => match j.getObjVal? "elem" with
      | .ok e => termUnknown s!"{path}.elem" e
      | _ => []
    | "container" => match j.getObjValAs? (Array Json) "fields" with
      | .ok fs => (fs.toList.zip (List.range fs.size)).flatMap (fun (f, i) => termUnknown s!"{path}.fields[{i}]" f)
      | _ => []
    | _ => []
  own ++ sub

/-- FNV-1a 64 of the file bytes (emit.py computes the same to bind a record to a file). -/
def fnv (b : ByteArray) : UInt64 :=
  b.foldl (fun h x => (h ^^^ x.toUInt64) * 1099511628211) 14695981039346656037

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

def checkFields (j : Json) (names : List String) (fs : List Desc) : Except String (List Line × Nat × List Nat) := do
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
      let cn := (c.getObjValAs? String "name").toOption
      let ci := (c.getObjValAs? Nat "index").toOption
      out := out ++ [(s!"name[{i}]", cn == some names[i]!, s!"claimed {cn}, term {names[i]!}"),
                     (s!"index[{i}]", ci == some i, s!"claimed {ci}, position {i}")]
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
  -- identity: schema, package, type (checker rules, not producer values)
  let schema := (j.getObjValAs? String "schema").toOption.getD ""
  let ty := (j.getObjValAs? String "type").toOption.getD ""
  let pk := (j.getObjValAs? String "package").toOption.getD ""
  let mut idl : List Line := [("schema", schema == "fvphase1c.desc/1", s!"schema '{schema}'"),
    ("type", goIdent ty, s!"type '{ty}' (non-empty ASCII identifier)"),
    ("package", knownPackages.contains pk, s!"package '{pk}' (checker-owned list)")]
  if handTypeNames.contains ty && handPackages.contains pk && (refs.lookup (pk, ty)).isNone then
    idl := idl ++ [("table-type", false, s!"table type name {ty} under package {pk}")]
  let unk := ((keysOf j).filter (fun x => !topKeys.contains x)) ++
    (match j.getObjValAs? (Array Json) "fields" with
     | .ok cs => (cs.toList.zip (List.range cs.size)).flatMap (fun (c, i) =>
         (keysOf c).filter (fun x => !claimKeys.contains x) |>.map (fun x => s!"fields[{i}].{x}"))
     | _ => []) ++
    (match j.getObjVal? "ssz" with | .ok t => termUnknown "ssz" t | _ => [])
  idl := idl ++ [("keys", unk.isEmpty, s!"unknown keys {unk}")]
  let d ← match (j.getObjVal? "ssz") >>= toDesc with
    | .ok d => pure d
    | .error e => return idl ++ [("parse", false, e)]
  let (names, fs) ← match d with
    | .container ns fs => pure (ns, fs)
    | _ => return idl ++ [("parse", false, "top level is not a container")]
  let mut out : List Line := idl ++ [("parse", true, "")]
  out := out ++ [("wf", (match d.wellFormed with | .ok _ => true | .error _ => false),
                  (match d.wellFormed with | .ok _ => "" | .error e => s!"{repr e}"))]
  let cf := optNat j "fixed_size"
  match cf with
  | .ok c => out := out ++ [("fixed", c == d.fixedSize, s!"claimed {c}, EthLib {d.fixedSize}")]
  | .error e => out := out ++ [("fixed", false, e)]
  match checkFields j names fs with
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
  let claimed : Option String := match j.getObjVal? "reference" with
    | .ok (.str r) => some r
    | .ok .null => none
    | .ok _ => some "<not a string>"
    | .error _ => none
  match refs.lookup (pk, ty) with
  | some (rname, rd, gd) =>
    out := out ++ [("ref-claim", claimed == some rname, s!"table {rname} for {pk}.{ty}, file {claimed}"),
                   ("ref", Desc.beq (posNames d) (posNames rd), s!"SPEC compared with {rname} (up to names)"),
                   ("go-names", Desc.beq d gd, s!"exact term with the checker's Go field names of {ty}")]
  | none =>
    out := out ++ [("ref-claim", claimed.isNone, s!"no spec Desc for {pk}.{ty}, file {claimed}")]
  return out

def fileKey (path : String) : IO (Option (String × String)) := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => return some ((j.getObjValAs? String "package").toOption.getD "", (j.getObjValAs? String "type").toOption.getD "")
  | .error _ => return none

/-- Check one list. Returns (pass, fail, spec, none, PASS-SPEC keys, all keys). -/
def runList (label : String) (paths : List String) :
    IO (Nat × Nat × Nat × Nat × List (String × String) × List (String × String)) := do
  let mut pass := 0
  let mut fail := 0
  let mut nspec := 0
  let mut nnone := 0
  let mut specKeys : List (String × String) := []
  let mut keys : List (String × String) := []
  for p in paths do
    let ls ← checkFile p
    let key ← fileKey p
    let st := match key with
      | some k => if (refs.lookup k).isSome then "SPEC" else "NONE"
      | none => "NONE"
    if st == "SPEC" then nspec := nspec + 1 else nnone := nnone + 1
    if let some k := key then keys := keys ++ [k]
    for (c, ok, det) in ls do
      let s := if det.startsWith "SKIP" then "SKIP" else if ok then "OK" else "FAIL"
      IO.println s!"DESCCHECK {p} {c} {s} {det}"
    let bad := ls.filter (fun l => !l.2.1) |>.map (·.1)
    let h := fnv (← IO.FS.readBinFile p)
    if bad.isEmpty then
      pass := pass + 1
      if st == "SPEC" then if let some k := key then specKeys := specKeys ++ [k]
      IO.println s!"DESCCHECK-FILE {p} PASS {st} {label} fnv={h}"
    else
      fail := fail + 1
      IO.println s!"DESCCHECK-FILE {p} FAIL {st} {label} fnv={h} {String.intercalate "," bad}"
  return (pass, fail, nspec, nnone, specKeys, keys)

def main : IO Unit := do
  let some list ← IO.getEnv "DESC_LIST" | throw (IO.userError "DESC_LIST is not set")
  -- self-check of the checker's own table: Go-named terms = Fv1 terms up to names; 21 names
  let mut selfOk := true
  for (k, (rname, rd, gd)) in refs do
    let ok := Desc.beq (posNames gd) (posNames rd)
    selfOk := selfOk && ok
    IO.println s!"DESCCHECK-TABLE-SELF {k.1}.{k.2} {rname} {if ok then "OK" else "FAIL"}"
  let topNames := refs.foldl (fun n (_, (_, _, gd)) => n + (match gd with | .container ns _ => ns.length | _ => 0)) 0
  IO.println s!"DESCCHECK-TABLE-SELF go-names {topNames} (expected 21)"
  selfOk := selfOk && topNames == 21
  let origs := (← IO.FS.readFile list).splitOn "\n" |>.filter (· ≠ "")
  let (op, of_, os, on, specKeys, keys) ← runList "original" origs
  -- coverage: every key of the checker's table exactly once as PASS SPEC among the originals;
  -- no (package, type) key twice among the originals
  let mut covOk := true
  for (k, (rname, _, _)) in refs do
    let n := (specKeys.filter (· == k)).length
    let ok := n == 1
    covOk := covOk && ok
    IO.println s!"DESCCHECK-COVERAGE {k.1}.{k.2} {rname} pass-spec={n} {if ok then "OK" else "FAIL"}"
  for k in keys.eraseDups do
    let n := (keys.filter (· == k)).length
    if n > 1 then
      covOk := false
      IO.println s!"DESCCHECK-DUPKEY {k.1}.{k.2} {n} FAIL"
  IO.println s!"DESCCHECK-DONE originals pass {op} fail {of_} spec {os} none {on}"
  match ← IO.getEnv "DESC_MUTANTS" with
  | some ml =>
    let ms := (← IO.FS.readFile ml).splitOn "\n" |>.filter (· ≠ "")
    let (mp, mf, msp, mn, _, _) ← runList "mutant" ms
    IO.println s!"DESCCHECK-DONE mutants pass {mp} fail {mf} spec {msp} none {mn}"
  | none => pure ()
  let allOk := selfOk && covOk && of_ == 0
  IO.println s!"DESCCHECK-TABLE {if allOk then "OK" else "FAIL"} self={selfOk} coverage={covOk} originals_failed={of_}"
  if !allOk then throw (IO.userError "DescCheck: table self-check, coverage or an original failed")

end DescCheck

#eval DescCheck.main
