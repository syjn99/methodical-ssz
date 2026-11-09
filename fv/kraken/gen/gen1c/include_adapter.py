"""The one adapter between the phase1c generator and the fix3 data-include API.

Every name and syntax of the include interface lives here and nowhere else.
Built against INCLUDE-API api_version 1 (status "committed", fix3 427708e;
snapshot in include-api-v1.json). An api_version change touches this file only.
"""
import json
import os

API_VERSION = 1
SNAPSHOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "include-api-v1.json")

DATA_DIR_IN_REPO = "fv/kraken/link/out/data/"   # where fix3 keeps data files (we never write there)
LEAN_NAMESPACE = "Fk.Data"
LEAN_INCLUDE = "data_include {id}"              # Lean command, Fk/Include.lean (fix3)


def check_api(path=SNAPSHOT):
    """Fail loudly if the given API file is not the version this adapter speaks."""
    d = json.load(open(path))
    if d.get("api_version") != API_VERSION:
        raise SystemExit(f"include adapter speaks api_version {API_VERSION}, {path} has {d.get('api_version')}")
    return d


def file_name(item_id):
    return f"{item_id}.data"


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


def lean_premise(item_id):
    """The premise shape a theorem uses for a data item (`Eq (bytes.At addr)`)."""
    return f"Eq ({bytes_name(item_id)}.At {addr_name(item_id)})"
