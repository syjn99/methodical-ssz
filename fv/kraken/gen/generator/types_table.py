"""Reader of the type table `gen/generator/types.tsv` for the Python tools. Python 3 standard library only.

The header comment of the table gives the columns.
`rows()` returns one dict for each row, in table order, with the keys of `COLUMNS` and `line` (the line number).
`options` and `companions` are lists; a "-" column is an empty list.
The reader stops with a message that names the line when a row is not valid.
A tool that writes a companion takes its types with `types_with(companion)`.
"""
import pathlib
import re
import sys

TABLE = pathlib.Path(__file__).resolve().parent / "types.tsv"
COLUMNS = ("package", "type", "mode", "options", "expect", "companions")
PACKAGES = {"v1alpha1": "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1",
            "v1": "github.com_OffchainLabs_prysm_v7_proto_engine_v1",
            "primitives": "github.com_OffchainLabs_prysm_v7_consensus_types_primitives"}
# mode: (method of the .S file, output file in lean/Prysm/<type>/, name part of the scratch files of gen.sh)
MODES = {"uint64": ("UnmarshalSSZ", "GeneratedDecodeAccept.lean", "uint64"),
         "decoder --whole-accept": ("UnmarshalSSZ", "GeneratedDecodeAccept.lean", "whole-accept"),
         "encoder --fast-path": ("MarshalSSZTo", "GeneratedEncodeFastPath.lean", "fast-path")}
# companion: the modes of the rows that can name it
COMPANIONS = {"spec": ("decoder --whole-accept", "encoder --fast-path"),
              "decode-spec": ("decoder --whole-accept",),
              "reject-witness": ("decoder --whole-accept",),
              "accept-witness": ("decoder --whole-accept",),
              "encode-spec": ("encoder --fast-path",),
              "negative-cases": ("decoder --whole-accept", "encoder --fast-path"),
              "hand-list": ("decoder --whole-accept", "encoder --fast-path")}
TYPE_COMPANIONS = ("spec", "hand-list")
NORM = "prysm/go1.26.10/link-set/norm"


def die(line, msg):
    sys.exit(f"{TABLE.name} line {line}: {msg}")


def rows():
    out, seen, per_type = [], set(), set()
    header = None
    for n, text in enumerate(TABLE.read_text().split("\n"), 1):
        if not text or text.startswith("#"):
            continue
        cols = text.split("\t")
        if header is None:
            if tuple(cols) != COLUMNS:
                die(n, f"the header must be {' TAB '.join(COLUMNS)}")
            header = cols
            continue
        if len(cols) != len(COLUMNS) or any(not c for c in cols):
            die(n, f"a row has {len(COLUMNS)} columns that are not empty, separated by one tab")
        r = dict(zip(COLUMNS, cols), line=n)
        if r["package"] not in PACKAGES:
            die(n, f"package {r['package']!r} is not one of {', '.join(PACKAGES)}")
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", r["type"]):
            die(n, f"type {r['type']!r} is not a Go type name")
        if r["mode"] not in MODES:
            die(n, f"mode {r['mode']!r} is not one of {', '.join(MODES)}")
        if r["expect"] not in ("accept", "refuse"):
            die(n, f"expect {r['expect']!r} is not accept or refuse")
        r["options"] = [] if r["options"] == "-" else r["options"].split(" ")
        r["companions"] = [] if r["companions"] == "-" else r["companions"].split(",")
        for c in r["companions"]:
            if c not in COMPANIONS:
                die(n, f"companion {c!r} is not one of {', '.join(COMPANIONS)}")
            if r["mode"] not in COMPANIONS[c]:
                die(n, f"companion {c} is not for mode {r['mode']}")
            if r["expect"] != "accept":
                die(n, f"companion {c} in a refuse row")
            if c in TYPE_COMPANIONS:
                if (r["type"], c) in per_type:
                    die(n, f"companion {c} is for the type: give it in one row of {r['type']}")
                per_type.add((r["type"], c))
        if (r["type"], r["mode"]) in seen:
            die(n, f"a second row for {r['type']} {r['mode']}")
        seen.add((r["type"], r["mode"]))
        out.append(r)
    if header is None:
        die(0, "no header line")
    return out


def types_with(companion, mode=None):
    """The type names of the rows that name `companion` (and have `mode`, if given), in table order, each name once."""
    if companion not in COMPANIONS:
        sys.exit(f"types_table: unknown companion {companion!r}")
    return list(dict.fromkeys(r["type"] for r in rows()
                              if companion in r["companions"] and (mode is None or r["mode"] == mode)))


def package_of(type_name):
    """The package of the rows of `type_name` (one package for each type)."""
    ps = {r["package"] for r in rows() if r["type"] == type_name}
    if len(ps) != 1:
        sys.exit(f"types_table: {type_name} has {len(ps)} packages in {TABLE.name}")
    return ps.pop()


def assembly(r):
    """The path of the `.S` file of the row, relative to fv/kraken."""
    return f"{NORM}/{PACKAGES[r['package']]}.{r['type']}.{MODES[r['mode']][0]}.S"


def output(r):
    """The path of the output of an accept row, relative to fv/kraken."""
    return f"lean/Prysm/{r['type']}/{MODES[r['mode']][1]}"


def kebab(s):
    """The Go type name in kebab case, for example deposit-request (file names and case ids)."""
    s = re.sub(r'(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])', '-', s)
    return re.sub(r'[^a-z0-9]+', '-', s.replace('_', '-').lower()).strip('-')
