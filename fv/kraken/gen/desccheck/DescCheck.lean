import Lean.Data.Json
import EthLib.Serialization.Ssz
import EthLib.Cryptography.Hash.Sha256
import Fv1.SpecScalars
import Fv1.SpecList
import Fv1.SpecFixedVec
import Fv1.SpecBitVec
import Fv1.SpecNested
import Fv1.SpecListC
import Fv1.SpecPrysm
import Fv1.SpecBitList

/-!
# Independent `Desc` checker (phase1c P3; closed-world design after review phase1c-r3)

Inputs (environment):
* `DESC_LIST`       the originals, one path per line
* `DESC_MUTANTS`    optional negative cases (recorded with role `mutant`; never count for the verdict)
* `DESC_RESULT`     the result file to write (JSON, written by Lean's JSON encoder)
* `DESC_INVENTORY`  the committed inventory (default `../prysm/inventory.json`); its sha256 is
                    printed and written into the result
* `DESC_BATCH`      test tooling: lines `id<TAB>list<TAB>result`, one closed-world run per line

Closed world. The expected key set is the checker's own table (9 hand types, Fv1 spec Desc and
21 Go field names) plus the (package, type) keys of the committed inventory (135). It never
comes from the producer's output. The originals must equal this set exactly: a missing, extra,
unkeyed or duplicate key, a duplicate path, or any failing original makes the verdict FAIL.

Per file (any failure = FAIL):
* `strict-json` the raw text: no duplicate key (after decoding escapes), integers only
                (`-?(0|[1-9][0-9]*)`), no byte-order mark, nothing after the top value
* `schema`      exactly `fvphase1c.desc/1`
* `type`        an ASCII Go identifier; `package` an ASCII path in the checker's package list
* `expected-key` (package, type) is in the expected set
* `hand-name`   a hand type name outside its table package, unless the key is in the
                checker-owned exception list (the real Prysm `v1alpha1.Checkpoint` and
                `v1alpha1.AttestationData`)
* `keys`        no unknown key at the top level or in a term; `claim-keys[i]` only the claim
                keys that apply to field i's kind
* `names`       every field name at every level is an ASCII Go identifier
* `parse`, `wf`, `fixed`, `nfields`, `width`, `variable`, `offset`, `kind`, `length`, `limit`,
  `elem`, `name`, `index`, `head`, `order`, `probe`: claims against EthLib functions
* table keys (status SPEC): `ref-claim` (the table's reference), `ref` (Fv1 spec Desc up to
  names), `go-names` (exact term with the checker's Go field names at every level)
* other keys (status NONE): `ref-claim` (no reference) and `inventory`: field names, head
  widths, variable flags, field kinds and fixed size equal the committed inventory. This binds a
  Prysm Desc to the inventory (same sszgen IR, another program). It is not a spec comparison.

Result file: schema `fvphase1c.desccheck-result/1`, inventory path and sha256, table keys,
exceptions, list-level findings, one record per file (path, sha256 of the bytes (EthLib
SHA-256, FIPS 180-4), role, package, type, status, PASS/FAIL, failed checks with details) and
`verdict` OK/FAIL. `gen1c/emit.py` reads only this file. The human log escapes every character
outside printable ASCII. A run with verdict FAIL ends with a non-zero exit.

Threat model. Defends against: producer or IR bugs in the 9 hand types (spec comparison),
mislabelled, stray, missing or duplicated Desc files, look-alike names, JSON parser differences,
and stale or mixed result files at the emit boundary (sha256 binding, verdict, inventory hash).
Does not defend against: wrong shapes of the 135 Prysm types that agree with the inventory
(no independent spec offline: consistency only), a forged result file written by hand (the
result is not signed), or a wrong inventory committed on purpose.

Run (gated): `cd fv/kraken/lean && DESC_LIST=<file> DESC_RESULT=<file> [DESC_MUTANTS=<file>] lake env lean ../gen/desccheck/DescCheck.lean`
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
def goIdent (s : String) : Bool :=
  !s.isEmpty && s.all (fun c => c.isAlphanum || c == '_') && !((s.toList.head?.map Char.isDigit).getD false)

/-- A package path: ASCII letters, digits, `.`, `_`, `-`, `/`; no empty segment, no `..`. -/
def pkgPath (s : String) : Bool :=
  !s.isEmpty && s.all (fun c => c.isAlphanum || c == '.' || c == '_' || c == '-' || c == '/') &&
    (s.splitOn "/").all (fun seg => !seg.isEmpty && seg != "." && seg != "..")

/-- Checker-owned exceptions: real Prysm types whose names equal hand type names. -/
def handNameExceptions : List (String × String) := [(prysmV1, "Checkpoint"), (prysmV1, "AttestationData")]

/-- Claim keys that apply to every field, and those that apply to one term kind only. -/
def claimBase : List String := ["name", "index", "offset", "width", "variable", "kind"]
def claimExtra : String → List String
  | "byteVector" | "bitVector" => ["length"] | "vector" => ["length", "elem_size"]
  | "byteList" | "bitList" => ["limit"] | "list" => ["limit", "elem_size"] | _ => []

def topKeys : List String :=
  ["schema", "type", "package", "ssz", "fixed_size", "fixed_part_size", "fields", "variable_order", "reference"]

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

def hexOf (b : ByteArray) : String :=
  b.foldl (fun acc x => acc ++ (if x < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 x.toNat)) ""

/-- SHA-256 (EthLib, FIPS 180-4) of the file bytes, lower-case hex. emit.py binds a record to a
file by this value (hashlib.sha256). -/
def sha256Hex (b : ByteArray) : String := hexOf (EthLib.Cryptography.Hash.sha256 b)

/-- Escape a string for the human log: every character outside printable ASCII becomes \x<hex>;. -/
def esc (s : String) : String :=
  s.foldl (fun acc c => if c.toNat >= 32 && c.toNat < 127 then acc.push c
    else acc ++ "\\x" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ ";") ""

/-! Strict JSON scan of the raw text (Lean's `Json.parse` keeps the last of duplicate keys and
accepts `1.6e1` and `16.0`; the producer's format allows neither). Errors: duplicate key in an
object (after decoding escapes), a number that is not `-?(0|[1-9][0-9]*)`, a byte-order mark,
content after the top value, a syntax error. -/
partial def skipWs (cs : Array Char) (i : Nat) : Nat :=
  if h : i < cs.size then (if cs[i] == ' ' || cs[i] == '\n' || cs[i] == '\t' || cs[i] == '\r' then skipWs cs (i + 1) else i) else i

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none

/-- Read a string starting at the opening quote; returns (decoded, next index) or none. -/
partial def scanStr (cs : Array Char) (i : Nat) (acc : String) : Option (String × Nat) :=
  if h : i < cs.size then
    let c := cs[i]
    if c == '"' then some (acc, i + 1)
    else if c == '\\' then
      if h2 : i + 1 < cs.size then
        let e := cs[i + 1]
        if e == 'u' then
          if i + 5 < cs.size then
            match hexVal cs[i+2]!, hexVal cs[i+3]!, hexVal cs[i+4]!, hexVal cs[i+5]! with
            | some a, some b, some c2, some d => scanStr cs (i + 6) (acc.push (Char.ofNat (((a * 16 + b) * 16 + c2) * 16 + d)))
            | _, _, _, _ => none
          else none
        else
          let m := if e == 'n' then '\n' else if e == 't' then '\t' else if e == 'r' then '\r'
                   else if e == 'b' then Char.ofNat 8 else if e == 'f' then Char.ofNat 12 else e
          scanStr cs (i + 2) (acc.push m)
      else none
    else scanStr cs (i + 1) (acc.push c)
  else none

partial def scanVal (cs : Array Char) (i0 : Nat) (path : String) (errs : Array String) : Option (Nat × Array String) := do
  let i := skipWs cs i0
  if h : i < cs.size then
    let c := cs[i]
    if c == '{' then
      let mut j := skipWs cs (i + 1)
      let mut seen : List String := []
      let mut es := errs
      if j < cs.size && cs[j]! == '}' then return (j + 1, es)
      repeat
        if !(j < cs.size && cs[j]! == '"') then failure
        let (k, j2) ← scanStr cs (j + 1) ""
        if seen.contains k then es := es.push s!"duplicate key {path}.{k}"
        seen := k :: seen
        let j3 := skipWs cs j2
        if !(j3 < cs.size && cs[j3]! == ':') then failure
        let (j4, es2) ← scanVal cs (j3 + 1) s!"{path}.{k}" es
        es := es2
        let j5 := skipWs cs j4
        if j5 < cs.size && cs[j5]! == ',' then j := skipWs cs (j5 + 1)
        else if j5 < cs.size && cs[j5]! == '}' then return (j5 + 1, es)
        else failure
      failure
    else if c == '[' then
      let mut j := skipWs cs (i + 1)
      let mut es := errs
      let mut n := 0
      if j < cs.size && cs[j]! == ']' then return (j + 1, es)
      repeat
        let (j2, es2) ← scanVal cs j s!"{path}[{n}]" es
        es := es2
        n := n + 1
        let j3 := skipWs cs j2
        if j3 < cs.size && cs[j3]! == ',' then j := skipWs cs (j3 + 1)
        else if j3 < cs.size && cs[j3]! == ']' then return (j3 + 1, es)
        else failure
      failure
    else if c == '"' then
      let (_, j) ← scanStr cs (i + 1) ""
      return (j, errs)
    else if c == '-' || c.isDigit then
      let mut j := i
      while j < cs.size && (cs[j]! == '-' || cs[j]! == '+' || cs[j]! == '.' || cs[j]! == 'e' || cs[j]! == 'E' || cs[j]!.isDigit) do
        j := j + 1
      let tok := String.ofList (cs.extract i j).toList
      let body := if tok.startsWith "-" then tok.drop 1 else tok
      let ok := !body.isEmpty && body.all Char.isDigit && (body == "0" || !body.startsWith "0")
      return (j, if ok then errs else errs.push s!"number form {path} '{tok}' (integers only)")
    else
      for lit in ["true", "false", "null"] do
        if String.ofList (cs.extract i (i + lit.length)).toList == lit then return (i + lit.length, errs)
      failure
  else failure

/-- Input bounds (R4-S2): a Desc is a few KB; the largest original is far below these. -/
def maxFileBytes : Nat := 1048576
def maxNesting : Nat := 64

/-- Maximum bracket nesting depth outside strings, in one linear pass (no recursion). -/
def maxDepth (txt : String) : Nat := Id.run do
  let mut d := 0
  let mut m := 0
  let mut inStr := false
  let mut escp := false
  for c in txt.toList do
    if inStr then
      if escp then escp := false
      else if c == '\\' then escp := true
      else if c == '"' then inStr := false
    else if c == '"' then inStr := true
    else if c == '{' || c == '[' then
      d := d + 1
      if d > m then m := d
    else if c == '}' || c == ']' then d := d - 1
  return m

/-- Strict-scan errors of a file text (empty list = clean). -/
def strictScan (txt : String) : List String :=
  let cs := txt.toList.toArray
  if cs.size > 0 && cs[0]! == Char.ofNat 0xFEFF then ["byte-order mark"]
  else match scanVal cs 0 "$" #[] with
    | none => ["JSON syntax (strict scan)"]
    | some (j, es) => es.toList ++ (if skipWs cs j < cs.size then ["content after the top value"] else [])

/-- All container field names of a term, at every level. -/
partial def allNames : Desc → List String
  | .vector e _ => allNames e
  | .list e _ => allNames e
  | .container ns fs => ns ++ fs.flatMap allNames
  | _ => []

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
      let allowed := claimBase ++ claimExtra (kindName f)
      let bad := (keysOf c).filter (fun x => !allowed.contains x)
      out := out ++ [(s!"claim-keys[{i}]", bad.isEmpty, s!"keys not allowed for kind {kindName f}: {bad}")]
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

/-- Inventory entry of a Prysm type: field names, per-field (head width, variable), per-field
term kind expected from the inventory shape, fixed size. -/
structure InvType where
  names : List String
  sizes : List (Nat × Bool)
  kinds : List String
  callees : List (Option (String × String))
  fixed : Option Nat

/-- The EthLib term kind that an inventory field shape stands for ("?" = no rule: FAIL). -/
def shapeKind (sh : String) : String :=
  if sh == "bytesN" then "byteVector" else if sh == "uint64" then "uint" else if sh == "bool" then "bool"
  else if sh == "bitvector" then "bitVector" else if sh == "bitlist" then "bitList"
  else if sh == "list[byte]" then "byteList"
  else if sh.startsWith "delegated overlay " then "uint"
  else if sh.startsWith "delegated container" then "container"
  else if sh.startsWith "list[" then "list" else if sh.startsWith "vector[" then "vector" else "?"

/-- The checker's closed world: the 9 table keys and the keys of the committed inventory. -/
structure Ctx where
  inv : List ((String × String) × InvType)
  expected : List (String × String)

structure FileRes where
  path : String
  sha : String
  key : Option (String × String)
  status : String
  lines : List Line
  deriving Inhabited

def FileRes.failed (r : FileRes) : List String := r.lines.filter (fun l => !l.2.1) |>.map (·.1)

def readInventory (j : Json) : Except String (List ((String × String) × InvType)) := do
  let ts ← j.getObjValAs? (Array Json) "types"
  ts.toList.mapM fun t => do
    let pk ← t.getObjValAs? String "package"
    let ty ← t.getObjValAs? String "name"
    let fs ← t.getObjValAs? (Array Json) "fields"
    let names ← fs.toList.mapM (·.getObjValAs? String "name")
    let sizes ← fs.toList.mapM fun f => do
      let w ← f.getObjValAs? Nat "fixed_size"
      let v ← f.getObjValAs? Bool "variable"
      pure (w, v)
    let kinds ← fs.toList.mapM fun f => do
      let sh ← f.getObjValAs? String "shape"
      pure (shapeKind sh)
    let callees ← fs.toList.mapM fun f => do
      match f.getObjVal? "callee" with
      | .ok (.str c) =>
        let parts := c.splitOn "/"
        pure (some (String.intercalate "/" parts.dropLast, parts.getLast!))
      | _ => pure none
    let fixed ← optNat t "fixed_size"
    let var ← t.getObjValAs? Bool "variable"
    pure ((pk, ty), { names, sizes, kinds, callees, fixed := if var then none else fixed })

/-- The container a field term stands for: itself, or the element of a list/vector. -/
def fieldContainer : Desc → Option Desc
  | .container ns fs => some (.container ns fs)
  | .list e _ => match e with | .container ns fs => some (.container ns fs) | _ => none
  | .vector e _ => match e with | .container ns fs => some (.container ns fs) | _ => none
  | _ => none

/-- Bind a container term to an inventory entry, and every delegated container field (or element)
recursively to its callee's entry (review phase1c-r4 R4-S3). Returns the mismatches. -/
partial def invMatch (inv : List ((String × String) × InvType)) (key : String × String) (d : Desc) (fuel : Nat) : List String :=
  if fuel == 0 then [s!"{key.2}: nesting deeper than the bound"] else
  match inv.lookup key, d with
  | none, _ => [s!"no inventory entry for {key.1}.{key.2}"]
  | some it, .container ns fs =>
    let sizes := fs.map (fun f => (f.fixedSize.getD bytesPerOffset, f.fixedSize.isNone))
    let kinds := fs.map kindName
    let own := (if ns == it.names then [] else [s!"{key.2}: names"]) ++ (if sizes == it.sizes then [] else [s!"{key.2}: head sizes"]) ++
      (if kinds == it.kinds then [] else [s!"{key.2}: kinds"]) ++ (if d.fixedSize == it.fixed then [] else [s!"{key.2}: fixed size"])
    let sub := (fs.zip it.callees).flatMap fun (f, c) =>
      match c, fieldContainer f with
      | some ck, some fc => if (inv.lookup ck).isSome then invMatch inv ck fc (fuel - 1) else []
      | _, _ => []
    own ++ sub
  | some _, _ => [s!"{key.2}: not a container"]

def checkFile (ctx : Ctx) (path : String) : IO FileRes := do
  let rd ← (IO.FS.readBinFile path).toBaseIO
  let bytes ← match rd with
    | .ok b => pure b
    | .error e => return { path, sha := "", key := none, status := "NONE", lines := [("read", false, s!"{e}")] }
  let sha := sha256Hex bytes
  let some txt := String.fromUTF8? bytes | return { path, sha, key := none, status := "NONE", lines := [("utf8", false, "not UTF-8")] }
  -- bounds before any parsing (review phase1c-r4 R4-S2): size and bracket nesting depth
  let depth := maxDepth txt
  if bytes.size > maxFileBytes || depth > maxNesting then
    return { path, sha, key := none, status := "NONE",
             lines := [("bounds", false, s!"size {bytes.size} (max {maxFileBytes}), nesting {depth} (max {maxNesting})")] }
  let strict := strictScan txt
  let mut idl : List Line := [("bounds", true, s!"size {bytes.size}, nesting {depth}"), ("strict-json", strict.isEmpty, s!"{strict}")]
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => return { path, sha, key := none, status := "NONE", lines := idl ++ [("json", false, e)] }
  -- identity: checker rules, closed world
  let schema := (j.getObjValAs? String "schema").toOption.getD ""
  let tyE := j.getObjValAs? String "type"
  let pkE := j.getObjValAs? String "package"
  let ty := tyE.toOption.getD ""
  let pk := pkE.toOption.getD ""
  let tyOk := tyE.toOption.isSome && goIdent ty
  let pkOk := pkE.toOption.isSome && pkgPath pk && knownPackages.contains pk
  idl := idl ++ [("schema", schema == "fvphase1c.desc/1", s!"schema '{schema}'"),
    ("type", tyOk, s!"type '{ty}' (ASCII Go identifier)"),
    ("package", pkOk, s!"package '{pk}' (ASCII path in the checker's package list)")]
  let key : Option (String × String) := if tyOk && pkOk then some (pk, ty) else none
  idl := idl ++ [("expected-key", (key.map ctx.expected.contains).getD false,
    s!"({pk}, {ty}) in the checker's expected set (table + committed inventory)")]
  if handTypeNames.contains ty && (refs.lookup (pk, ty)).isNone && !handNameExceptions.contains (pk, ty) then
    idl := idl ++ [("hand-name", false, s!"hand type name {ty} outside its table package and not a listed exception")]
  let missingTop := topKeys.filter (fun x => !(keysOf j).contains x)
  idl := idl ++ [("required-keys", missingTop.isEmpty, s!"missing top-level keys {missingTop}")]
  let unk := ((keysOf j).filter (fun x => !topKeys.contains x)) ++
    (match j.getObjVal? "ssz" with | .ok t => termUnknown "ssz" t | _ => [])
  idl := idl ++ [("keys", unk.isEmpty, s!"unknown keys {unk}")]
  let status := if (refs.lookup (pk, ty)).isSome then "SPEC" else "NONE"
  let d ← match (j.getObjVal? "ssz") >>= toDesc with
    | .ok d => pure d
    | .error e => return { path, sha, key, status, lines := idl ++ [("parse", false, e)] }
  let (names, fs) ← match d with
    | .container ns fs => pure (ns, fs)
    | _ => return { path, sha, key, status, lines := idl ++ [("parse", false, "top level is not a container")] }
  let badNames := (allNames d).filter (fun n => !goIdent n)
  let mut out : List Line := idl ++ [("parse", true, ""), ("names", badNames.isEmpty, s!"names that are not ASCII Go identifiers: {badNames}")]
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
    -- binding of a Prysm Desc to the committed inventory (same IR, other program; not a spec)
    match ctx.inv.lookup (pk, ty) with
    | some _ =>
      let mism := invMatch ctx.inv (pk, ty) d 16
      out := out ++ [("inventory", mism.isEmpty, s!"names/sizes/kinds/fixed vs inventory, delegated containers recursively: {mism}")]
      -- the two excepted Prysm types must have the hand spec shape (Fv1) up to names
      if handNameExceptions.contains (pk, ty) then
        match refs.find? (fun (k, _) => k.2 == ty) with
        | some (_, (rname, rd, _)) =>
          out := out ++ [("exception-shape", Desc.beq (posNames d) (posNames rd), s!"excepted {ty} vs {rname} up to names")]
        | none => out := out ++ [("exception-shape", false, s!"no Fv1 Desc for excepted {ty}")]
    | none => out := out ++ [("inventory", false, s!"no inventory entry for ({pk}, {ty})")]
  return { path, sha, key, status, lines := out }

def keyStr (k : String × String) : String := s!"{k.1}.{k.2}"

def recordJson (role : String) (r : FileRes) : Json :=
  Json.mkObj [("path", r.path), ("sha256", r.sha), ("role", role),
    ("package", match r.key with | some k => Json.str k.1 | none => Json.null),
    ("type", match r.key with | some k => Json.str k.2 | none => Json.null),
    ("status", r.status), ("result", if r.failed.isEmpty then "PASS" else "FAIL"),
    ("failed", Json.arr (r.failed.map Json.str).toArray),
    ("failed_detail", Json.arr ((r.lines.filter (fun l => !l.2.1)).map (fun l => Json.mkObj [("check", l.1), ("detail", l.2.2)])).toArray)]

/-- Check a list of originals (closed world) and optional mutants; return the result JSON and verdict. -/
def runSet (ctx : Ctx) (invInfo : Json) (selfOk : Bool) (cache : IO.Ref (Std.HashMap String FileRes))
    (origs : List String) (muts : List String) (quiet : Bool) : IO (Json × Bool) := do
  let check (p : String) : IO FileRes := do
    match (← cache.get).get? p with
    | some r => pure r
    | none =>
      let r ← checkFile ctx p
      cache.modify (·.insert p r)
      pure r
  let mut recs : Array Json := #[]
  let mut ores : Array FileRes := #[]
  for p in origs do
    let r ← check p
    ores := ores.push r
    recs := recs.push (recordJson "original" r)
    unless quiet do
      for (c, ok, det) in r.lines do
        IO.println (esc s!"DESCCHECK {p} {c} {if det.startsWith "SKIP" then "SKIP" else if ok then "OK" else "FAIL"} {det}")
      IO.println (esc s!"DESCCHECK-FILE {p} {if r.failed.isEmpty then "PASS" else "FAIL"} {r.status} original {String.intercalate "," r.failed}")
  for p in muts do
    let r ← check p
    recs := recs.push (recordJson "mutant" r)
    unless quiet do
      for (c, ok, det) in r.lines do
        IO.println (esc s!"DESCCHECK {p} {c} {if det.startsWith "SKIP" then "SKIP" else if ok then "OK" else "FAIL"} {det}")
      IO.println (esc s!"DESCCHECK-FILE {p} {if r.failed.isEmpty then "PASS" else "FAIL"} {r.status} mutant {String.intercalate "," r.failed}")
  -- list level: the originals must be exactly the expected set
  let keys := ores.toList.filterMap (·.key)
  let missing := ctx.expected.filter (fun k => !keys.contains k)
  let extra := (keys.filter (fun k => !ctx.expected.contains k)).eraseDups
  let unkeyed := ores.toList.filter (·.key.isNone) |>.map (·.path)
  let dupKeys := keys.eraseDups.filter (fun k => (keys.filter (· == k)).length > 1)
  let paths := origs
  let dupPaths := paths.eraseDups.filter (fun p => (paths.filter (· == p)).length > 1)
  let failedOrig := ores.toList.filter (fun r => !r.failed.isEmpty) |>.map (·.path)
  let ok := selfOk && missing.isEmpty && extra.isEmpty && unkeyed.isEmpty && dupKeys.isEmpty && dupPaths.isEmpty && failedOrig.isEmpty
  let ks (l : List (String × String)) := Json.arr (l.map (fun k => Json.mkObj [("package", k.1), ("type", k.2)])).toArray
  let res := Json.mkObj [("schema", "fvphase1c.desccheck-result/1"), ("checker", "fv/kraken/gen/desccheck/DescCheck.lean"),
    ("inventory", invInfo), ("table_keys", Json.arr (refs.map (fun (k, (rn, _, _)) => Json.mkObj [("package", k.1), ("type", k.2), ("reference", rn)])).toArray),
    ("hand_name_exceptions", ks handNameExceptions), ("expected_key_count", ctx.expected.length),
    ("originals", origs.length), ("mutants", muts.length),
    ("list", Json.mkObj [("missing", ks missing), ("extra", ks extra), ("unkeyed", Json.arr (unkeyed.map Json.str).toArray),
      ("duplicate_keys", ks dupKeys), ("duplicate_paths", Json.arr (dupPaths.map Json.str).toArray),
      ("failed_originals", Json.arr (failedOrig.map Json.str).toArray), ("table_self_check", selfOk)]),
    ("records", Json.arr recs), ("verdict", if ok then "OK" else "FAIL")]
  unless quiet do
    IO.println (esc s!"DESCCHECK-LIST missing {missing.map keyStr} extra {extra.map keyStr} unkeyed {unkeyed} dupkeys {dupKeys.map keyStr} duppaths {dupPaths} failed {failedOrig.length}")
  return (res, ok)

def readList (p : String) : IO (List String) := do
  return (← IO.FS.readFile p).splitOn "\n" |>.filter (· ≠ "")

def main : IO Unit := do
  -- the closed world: table (checker-owned) + committed inventory (bound by sha256)
  let invPath := (← IO.getEnv "DESC_INVENTORY").getD "../prysm/inventory.json"
  let invBytes ← IO.FS.readBinFile invPath
  let invSha := sha256Hex invBytes
  let some invTxt := String.fromUTF8? invBytes | throw (IO.userError "inventory is not UTF-8")
  let invJ ← IO.ofExcept (Json.parse invTxt)
  let inv ← IO.ofExcept (readInventory invJ)
  let ctx : Ctx := { inv, expected := refs.map (·.1) ++ inv.map (·.1) }
  IO.println s!"DESCCHECK-INVENTORY {esc invPath} sha256={invSha} keys={inv.length} expected={ctx.expected.length}"
  -- self-check of the checker's own tables
  let mut selfOk := true
  for (k, (rname, rd, gd)) in refs do
    let ok := Desc.beq (posNames gd) (posNames rd)
    selfOk := selfOk && ok
    IO.println s!"DESCCHECK-TABLE-SELF {k.1}.{k.2} {rname} {if ok then "OK" else "FAIL"}"
  let topNames := refs.foldl (fun n (_, (_, _, gd)) => n + (match gd with | .container ns _ => ns.length | _ => 0)) 0
  selfOk := selfOk && topNames == 21
  let exOk := handNameExceptions.all (fun k => (inv.lookup k).isSome)
  let overlap := refs.filter (fun (k, _) => (inv.lookup k).isSome) |>.length
  let dupExpected := ctx.expected.length != ctx.expected.eraseDups.length
  let invPkgOk := inv.all (fun (k, _) => k.1 == prysmV1 || k.1 == prysmEngine)
  IO.println s!"DESCCHECK-TABLE-SELF inventory-keys-in-prysm-packages={invPkgOk}"
  selfOk := selfOk && exOk && overlap == 0 && !dupExpected && invPkgOk
  IO.println s!"DESCCHECK-TABLE-SELF go-names={topNames} (21) exceptions-in-inventory={exOk} table-inventory-overlap={overlap} duplicate-expected={dupExpected} ok={selfOk}"
  let invInfo := Json.mkObj [("path", invPath), ("sha256", invSha), ("keys", inv.length)]
  let cache ← IO.mkRef ({} : Std.HashMap String FileRes)
  -- batch of list scenarios: one result file each (test tooling; exit 0 if all ran)
  if let some bp := ← IO.getEnv "DESC_BATCH" then
    for line in ← readList bp do
      match line.splitOn "\t" with
      | [sid, lp, rp] =>
        let (res, ok) ← runSet ctx invInfo selfOk cache (← readList lp) [] true
        IO.FS.writeFile rp (res.pretty ++ "\n")
        IO.println (esc s!"DESCCHECK-SCENARIO {sid} {if ok then "OK" else "FAIL"}")
      | _ => throw (IO.userError s!"bad batch line {esc line}")
    return
  let some list ← IO.getEnv "DESC_LIST" | throw (IO.userError "DESC_LIST is not set")
  let some resPath ← IO.getEnv "DESC_RESULT" | throw (IO.userError "DESC_RESULT is not set")
  let muts ← match ← IO.getEnv "DESC_MUTANTS" with
    | some m => readList m
    | none => pure []
  let (res, ok) ← runSet ctx invInfo selfOk cache (← readList list) muts false
  IO.FS.writeFile resPath (res.pretty ++ "\n")
  IO.println s!"DESCCHECK-VERDICT {if ok then "OK" else "FAIL"}"
  if !ok then throw (IO.userError "DescCheck: verdict FAIL (see the result file)")

end DescCheck

#eval DescCheck.main
