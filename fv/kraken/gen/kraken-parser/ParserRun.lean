import Kraken.X64.Parser

/-!
Run the pinned Kraken runtime x64 parser (the one behind `include_x64_code` in
`Machine/Include.lean`) on every `.S` file listed in `$PARSER_RUN_LIST`, one path per
line. Prints `parser OK <file> <directives>` or `parser ERR <file> <message>`,
then `parser DONE <ok> <err>`. `<file>` is the file name without its directory, so the output holds no machine path.
Read-only; no declaration is added.

Run (a heavy job): `cd fv/kraken/lean && PARSER_RUN_LIST=<file> lake env lean ../gen/kraken-parser/ParserRun.lean`
-/

def parserRunMain : IO Unit := do
  let some list ← IO.getEnv "PARSER_RUN_LIST" | throw (IO.userError "PARSER_RUN_LIST is not set")
  let paths := (← IO.FS.readFile list).splitOn "\n" |>.filter (· ≠ "")
  let mut ok := 0
  let mut err := 0
  for p in paths do
    let s ← IO.FS.readFile p
    let name := (System.FilePath.mk p).fileName.getD p
    match Kraken.X64.Parser.parse (Kraken.Parser.stripDirectives s) with
    | .ok prog =>
      ok := ok + 1
      IO.println s!"parser OK {name} {prog.length}"
    | .error e =>
      err := err + 1
      IO.println s!"parser ERR {name} {e}"
  IO.println s!"parser DONE {ok} {err}"

#eval parserRunMain
