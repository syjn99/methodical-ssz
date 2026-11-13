"""The one adapter between the first generator and the data-include API.

Every name and syntax of the include interface lives here and nowhere else.
Built against the include API version 3 (snapshot include-api-v3.json; the status and commit fields of that record
are checked below). v3 = the 22 items
of v2 unchanged + lcFmtItems ("Items: %w"). v2 (commit d9cdb40) and v1 are history.
v1 -> v2: names and file format unchanged; an address term at offset 0 has no `+ 0`.
An api_version change touches this file only.
"""
import json
import os

API_VERSION = 3
API_STATUS = "approved (final, stage B)"
API_FIX3_COMMIT = "f9e2bc3dc02ed3521e33b04b4bdaeb9c1fa5f3fe"
SNAPSHOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "include-api-v3.json")
# old data id of the snapshot -> present id of the data file (link/out/data-ids-old-new.tsv)
PRESENT_ID = {l.split("\t")[0]: l.split("\t")[1] for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
              "..", "..", "link", "out", "data-ids-old-new.tsv")).read().split("\n")
              if l and not l.startswith(("#", "old id\t"))}

DATA_DIR_IN_REPO = "fv/kraken/link/out/data/"   # where the data files are kept (we never write there)
LEAN_NAMESPACE = "TestTarget.Data"
LEAN_INCLUDE = "data_include {id}"              # Lean command, Machine/Include.lean

# Labels are convert_objdump.py-cleaned symbol names (API data_files.format).
RODATA_SYMBOL = "go:string.*"                   # ELF group symbol of Go string data
RODATA_LABEL = "go_string._"                    # its cleaned label in .S files and data files
ERR_GLOBAL_LABEL_RE = r"\b(ssz\.Err\w+)(?:\+\d+)?\(%rip\)"   # error-global references in a .S file
RODATA_REF_RE = r"go_string\._\+(\d+)\(%rip\)"            # rodata offsets referenced in a .S file


def err_global_id(label):
    """API id of an error global: `ssz.ErrSize` -> `ErrSize` (one id per global, address only)."""
    return label.split(".", 1)[1]


def rodata_id(gen_id, label, off, length, api=None):
    """The API item id for a rodata range, if the API table lists the same (label, offset, length);
    otherwise the generator's own id. Returns (id, api_id or None)."""
    api = api or check_api()
    for it in api["items"]:
        if it.get("label") == label and it.get("offset") == off and it.get("length") == length:
            return it["id"], it["id"]
    return gen_id, None


def check_api(path=SNAPSHOT):
    """Fail loudly if the given API file is not the version this adapter speaks."""
    d = json.load(open(path))
    if d.get("api_version") != API_VERSION:
        raise SystemExit(f"include adapter speaks api_version {API_VERSION}, {path} has {d.get('api_version')}")
    if d.get("status") != API_STATUS or d.get("fix3_commit") != API_FIX3_COMMIT:
        raise SystemExit(f"include adapter is built against {API_STATUS} at {API_FIX3_COMMIT}, {path} has "
                         f"{d.get('status')!r} at {d.get('fix3_commit')!r}")
    return d


def file_name(item_id):
    """Data file of an API item. The snapshot include-api-v3.json is a record and keeps the old ids;
    link/out/data-ids-old-new.tsv gives the present id of each data file of link/out."""
    return f"{PRESENT_ID.get(item_id, item_id)}.data"


def bytes_name(item_id):
    return f"{LEAN_NAMESPACE}.{item_id}"


def addr_name(item_id):
    return f"{LEAN_NAMESPACE}.{item_id}_addr"


def render(item_id, label, off, data=None, words=()):
    """Text of one data file: `at`, then `bytes` lines (16 per line) and `word` lines.

    words: (position, label, off) in byte order inside data; a word replaces 8 bytes.
    """
    out = [f"# {item_id}", f"at {label} {off}"]
    if data is not None:
        pos, wi = 0, sorted(words)
        while pos < len(data):
            if wi and wi[0][0] == pos:
                _, wl, wo = wi.pop(0)
                out.append(f"word {wl} {wo}")
                pos += 8
                continue
            end = min(len(data), pos + 16, wi[0][0] if wi else len(data))
            out.append("bytes " + " ".join(f"{b:02x}" for b in data[pos:end]))
            pos = end
    return "\n".join(out) + "\n"


def addr_term(label, off):
    """Lean address term of `at <label> <off>` (v2: no `+ 0` for offset 0)."""
    return f'(label "{label}").toBitVec' if off == 0 else f'(label "{label}" + {off}).toBitVec'


def lean_premise(item_id):
    """The premise shape a theorem uses for a data item (`Eq (bytes.At addr)`)."""
    return f"Eq ({bytes_name(item_id)}.At {addr_name(item_id)})"
