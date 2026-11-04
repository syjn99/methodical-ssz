import Kraken.X64.Parser
/-! Runtime-parser check: parse each line of each .S file given on the command
line with `Kraken.X64.Parser.parse`, print the lines it rejects. -/
def main (args : List String) : IO UInt32 := do
  let mut bad := 0
  for f in args do
    let ls := (← IO.FS.readFile f).splitOn "\n"
    let mut fails : List String := []
    for l in ls do
      match Kraken.X64.Parser.parse l with
      | .ok _ => pure ()
      | .error e => fails := fails ++ [s!"  {l.trimAscii} -- {e}"]
    IO.println s!"{f}: {ls.length - 1} lines, {fails.length} rejected"
    for x in fails do IO.println x
    bad := bad + fails.length
  return if bad == 0 then 0 else 1
