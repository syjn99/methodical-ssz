#!/usr/bin/env python3
"""Make the link set of the Prysm target from the ELF and its listings, with the item table.

Usage (Python 3 standard library only; run from any directory):
  link_set.py <outdir> <elf> <objdump> <nm> [<table>]

  <elf>      the Prysm target ELF
  <objdump>  `go tool objdump -gnu` of the ELF
  <nm>       `go tool nm -size -sort address` of the ELF
  <table>    the item table. Default: fv/kraken/prysm/go1.26.10/link-set.tsv

The command writes into <outdir>:
  target.objdump     the functions of the table, in the order of <objdump>
  target-amd64       a link to <elf>
  target-amd64.nm    a link to <nm>
  norm/              the output of `link/convert_objdump.py --norm`: one .S file per function and all.S
  data/              one data file per data row of the table (format in link/README.md section 5)
Then run `link/check.py <outdir>`. The tracked copy of the set is fv/kraken/prysm/go1.26.10/link-set.

The table is tab-separated text with a header line. It has one row per function and one row per data item.
  kind      `function` or `data`
  go_type   function: the receiver type with its import path. data: the Go type of the value at the address
  name      function: the method name. data: the data id, which is also the file name `<id>.data`
  what      plain words: what the row is
  label, offset, length
            data only: the address is the label plus the offset. The label is the short name of convert_objdump.py
  used_by   data only: `<go_type>.<method>` of a function whose converted code names the address, or `-`
For the Go types `internal/abi.Type` and `internal/abi.ITab`, the pointer slots of the value come from the Go layout
(LAYOUT below). They become `word` lines. The other types have no pointer slots.

Before it writes a data file, the command checks each data row against the converted code:
- If `used_by` is not `-`, the .S file of that function has the operand `<label>+<offset>(%rip)`.
- For a `string` row, `what` holds the text in double quotes, the ELF has that text at the address, and
  `length` is its length. The function loads the length with `mov $<length>,%ebx` after the operand.
- For a row of a LAYOUT type, `length` is the size of the type.
Exit 1 if a check fails or a function of the table is not in <objdump>.
"""
import importlib.util
import json
import os
import pathlib
import re
import subprocess
import sys

KRAKEN = pathlib.Path(__file__).resolve().parents[2]
TABLE = KRAKEN / "prysm/go1.26.10/link-set.tsv"
COLUMNS = ["kind", "go_type", "name", "what", "label", "offset", "length", "used_by"]
# Go type -> (size in bytes, offsets of the 8-byte pointer slots)
LAYOUT = {
    "internal/abi.Type": (48, [24, 32]),  # the Equal func and GCData pointers
    "internal/abi.ITab": (32, [0, 8, 24]),  # Inter, Type, Fun[0]
}


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def read_table(path):
    lines = pathlib.Path(path).read_text().splitlines()
    if lines[0].split("\t") != COLUMNS:
        sys.exit(f"{path}: the header is not {COLUMNS}")
    rows = [dict(zip(COLUMNS, line.split("\t"))) for line in lines[1:]]
    for r in rows:
        if r["kind"] not in ("function", "data") or len(r) != len(COLUMNS):
            sys.exit(f"{path}: bad row {r}")
    return rows


def symbol(go_type, method):
    """The Go symbol of a method with a pointer receiver: `<import path>.(*<Type>).<Method>`."""
    path, typ = go_type.rsplit(".", 1)
    return f"{path}.(*{typ}).{method}"


def filter_objdump(rows, objdump, out):
    want = {symbol(r["go_type"], r["name"]) for r in rows if r["kind"] == "function"}
    keep, cur, seen = [], False, set()
    for line in open(objdump):
        if line.startswith("TEXT "):
            name = line.split()[1].removesuffix("(SB)")
            cur = name in want
            if cur:
                seen.add(name)
        if cur:
            keep.append(line)
    (out / "target.objdump").write_text("".join(keep))
    missing = sorted(want - seen)
    print(f"functions {len(seen)} missing {missing}")
    return not missing


def check_rows(rows, data, out):
    """The checks of the usage text. Returns the item list of link/data.py."""
    elf, secs = data.read_elf(out / "target-amd64")
    by = data.symbols(data.conv.read_nm(out / "target-amd64.nm"))
    errors, items = [], []
    for r in (r for r in rows if r["kind"] == "data"):
        label, offset, length = r["label"], int(r["offset"]), int(r["length"])
        size, words = LAYOUT.get(r["go_type"], (None, []))
        if size is not None and size != length:
            errors.append(f"{r['name']}: length {length}, but {r['go_type']} has {size} bytes")
        if r["used_by"] != "-":
            go_type, method = r["used_by"].rsplit(".", 1)
            code = (out / "norm" / f"{data.clean(symbol(go_type, method))}.S").read_text().split("\n")
            operand = f"{label}+{offset}(%rip)" if offset else f"{label}(%rip)"
            at = [i for i, line in enumerate(code) if operand in line]
            if not at:
                errors.append(f"{r['name']}: {r['used_by']} has no operand {operand}")
            elif r["go_type"] == "string" and not any(
                    code[i + 1].strip() == f"mov ${length:#x},%ebx" for i in at if i + 1 < len(code)):
                errors.append(f"{r['name']}: {r['used_by']} loads no length {length} after {operand}")
        if r["go_type"] == "string":
            m = re.search(r'"(.*)"', r["what"])
            addresses = {a for a, _, _ in by.get(label, set())}
            if not m or len(addresses) != 1:
                errors.append(f"{r['name']}: no quoted text, or the label does not name one address")
            else:
                text = json.loads(f'"{m[1]}"').encode()
                got = data.elf_bytes(elf, secs, addresses.pop() + offset, length)
                if got != text:
                    errors.append(f"{r['name']}: the ELF has {got!r}, the table has {text!r}")
        items.append((r["name"], label, offset, length, words))
    for e in errors:
        print("FAIL", e)
    return items, not errors


def main(outdir, elf, objdump, nm, table=TABLE):
    rows = read_table(table)
    out = pathlib.Path(outdir)
    (out / "norm").mkdir(parents=True, exist_ok=True)
    if not filter_objdump(rows, objdump, out):
        return 1
    for src, dst in ((elf, "target-amd64"), (nm, "target-amd64.nm")):
        p = out / dst
        if not p.is_symlink() and not p.exists():
            os.symlink(os.path.abspath(src), p)
    r = subprocess.run([sys.executable, "-I", "-B", str(KRAKEN / "link/convert_objdump.py"), str(out / "target.objdump"),
                        str(out / "target-amd64.nm"), str(out / "norm"), "--norm"])
    if r.returncode != 0:
        print(f"FAIL convert_objdump.py: exit {r.returncode}")
        return 1
    data = load(KRAKEN / "link/data.py", "data")
    items, ok = check_rows(rows, data, out)
    if not ok:
        return 1
    data.ITEMS = items
    data.main(out)
    print(f"data files {len(items)}")
    return 0


if __name__ == "__main__":
    if len(sys.argv) not in (5, 6):
        sys.exit(__doc__)
    sys.exit(main(*sys.argv[1:]))
