import Kraken.X64.Parser

/-!
Run the pinned Kraken runtime x64 parser (the one behind `include_x64_rt` in
`Machine/Include.lean`) on every `.S` file listed in `$PARSER_RUN_LIST`, one path per
line. Prints `KPARSE OK <path> <directives>` or `KPARSE ERR <path> <message>`,
then `KPARSE DONE <ok> <err>`. Read-only; no declaration is added.

Run (gated): `cd fv/kraken/lean && PARSER_RUN_LIST=<file> lake env lean ../gen/kraken-parser/ParserRun.lean`
-/

def parserRunMain : IO Unit := do
  let some list ← IO.getEnv "PARSER_RUN_LIST" | throw (IO.userError "PARSER_RUN_LIST is not set")
  let paths := (← IO.FS.readFile list).splitOn "\n" |>.filter (· ≠ "")
  let mut ok := 0
  let mut err := 0
  for p in paths do
    let s ← IO.FS.readFile p
    match Kraken.X64.Parser.parse (Kraken.Parser.stripDirectives s) with
    | .ok prog =>
      ok := ok + 1
      IO.println s!"KPARSE OK {p} {prog.length}"
    | .error e =>
      err := err + 1
      IO.println s!"KPARSE ERR {p} {e}"
  IO.println s!"KPARSE DONE {ok} {err}"

#eval parserRunMain
