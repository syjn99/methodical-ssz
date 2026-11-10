#!/usr/bin/env python3
"""Scalability stage S0 (NEXT-PLAN after MS1): freeze the hand-proof cost baseline per unit. No proving, no target.

Usage: baseline.py <COST.json> <logs-dir> <events-dir> <lean-dir> <BASELINE.json>
Inputs, all saved before this program runs:
- COST.json (gen/e2e/cost.py: gate records + job logs): per module runs, failed runs, probes, gate seconds, peak RSS,
  memcap kills; per job start time, gate seconds, class.
- logs-dir: job logs (`== <module>` lines mark the modules that a multi-module job built).
- events-dir: the worker event logs opus-events*.jsonl (tool calls with timestamps).
- lean-dir: fv/kraken/lean (hand-written proof lines are counted in the committed files).
Definitions (also written into the output):
- unit cost = sum over the unit's modules of the COST.json per-module numbers; peak = max; a module shared by two units
  is counted in both and listed in `shared_modules`.
- multi_module_jobs: jobs that built a unit module next to other modules (cost.py keeps their gate time with the job,
  so the module rows show 0 s for them); their gate seconds are listed, not added.
- proof_lines: lines of the unit's committed .lean files; `code_lines` = without blank lines, `--` lines and `/- -/` blocks.
- first_edit_utc: earliest event timestamp of a Write/Edit tool call on a unit file, or of a Bash call whose command text
  writes a unit file (redirect, `open(`, `sed -i`, `cp`, `mv`); accept_utc: per module, the end of the first exit-0 run
  after the module's last failed run; unit = max over modules. wall_clock_s = accept - first_edit. first_accept_utc: per
  module the end of its first exit-0 run; unit = max over modules (every module of the unit built once);
  wall_clock_first_accept_s = first_accept - first_edit. Later follow-up fixes (review items) move accept_utc, not
  first_accept_utc. Both are spans: they include work on other units in between (sessions interleave units). Python 3 stdlib only.
"""
import datetime
import json
import pathlib
import re
import sys

UNITS = {
    "epoch_decoder": {"note": "accept (E2, session 1) and the length reject (INBOX 004, session 1); later follow-up N3/N5 (session 3)", "modules": ["E2e.Epoch", "E2e.WitEp", "E2e.EpReject", "E2e.WitEpR"]},
    "slot_decoder": {"note": "A2 (session 3); E2eAd.Prims holds both Slot and CommitteeIndex: its cost is in both rows", "modules": ["E2eAd.Prims", "E2eAd.WitSl"]},
    "committee_index_decoder": {"note": "A2 (session 3); E2eAd.Prims shared with the Slot row", "modules": ["E2eAd.Prims", "E2eAd.WitCi"]},
    "checkpoint_decoder": {"note": "E3 accept/reject/spec (session 1), witnesses S6 (session 2), CpUAccC function spec (A2, session 3); E2eAd.CpSpecs shared with the encoder row", "modules": ["E2e.CpAccept", "E2e.WitCpA", "E2e.CpReject", "E2e.WitCpR", "E2e.CpSpecK",
                                       "E2e.WitCpAS", "E2e.WitCpRS", "E2eAd.CpSpecs", "E2eAd.WitCpSpecs"]},
    "checkpoint_encoder": {"note": "fast path (session 1), reject (INBOX 004), first growslice site (session 2), INBOX 009 (session 4), INBOX 010 M1/M2/S1 (session 5); CpMAccC; E2eAd.CpSpecs shared", "modules": ["E2e.CpMarshal", "E2e.WitCpM", "E2e.CpMarshalR", "E2e.WitCpMR", "E2e.CpSpecM",
                                       "E2e.WitCpS", "E2e.CpMarshalG", "E2e.WitCpG", "E2e.CpWHead", "E2e.CpWTail",
                                       "E2e.CpWTailG", "E2e.CpWGrow", "E2e.CpWGrowAny", "E2e.CpWCover", "E2e.WitCpW",
                                       "E2e.WitCpWR", "E2e.CpWSharp", "E2e.CpWCoverF", "E2e.WitCpWF", "E2e.WitCpWRF",
                                       "E2e.GoValW", "E2e.ProbeW", "E2e.ProbeWW", "E2eAd.CpSpecs", "E2eAd.WitCpMS"]},
    "attestation_data_decoder": {"note": "A3 (session 4): 4 segments, main, reject, spec, unreachable lemmas, witnesses, BumpNew72 model", "modules": ["E2eAd.AdHead", "E2eAd.AdRoot", "E2eAd.AdSrc", "E2eAd.AdTgt",
                                             "E2eAd.AdAccept", "E2eAd.AdReject", "E2eAd.AdSpecK", "E2eAd.WitAdA",
                                             "E2eAd.WitAdR", "E2eAd.BumpNew72", "E2eAd.Spec", "E2eAd.ProbeAd"]},
}
NOT_ATTRIBUTED = ("shared infrastructure, composition and generated files (not in any unit): E2e.Code, E2e.Data, "
                  "E2e.Include, E2e.Layout, E2e.Spec, E2e.SpecEq, E2e.SpecChecker, E2e.GoVal, E2e.Compose, "
                  "E2e.CpCompose, E2e.WitCpC, E2eAd.Code, E2eAd.Data, E2eAd.Include, E2eAd.Layout, E2eAd.SpecChecker")


def ts(s):
    return datetime.datetime.fromisoformat(s.replace("Z", "+00:00"))


def code_lines(text):
    n, block = 0, 0
    for line in text.split("\n"):
        t = line.strip()
        if block:
            block += t.count("/-") - t.count("-/")
            continue
        if t.startswith("/-"):
            block = t.count("/-") - t.count("-/")
            continue
        if not t or t.startswith("--"):
            continue
        n += 1
    return n


def main(cost_p, logs_d, ev_d, lean_d, out_p):
    cost = json.load(open(cost_p))
    pm, jobs = cost["per_module"], cost["jobs"]
    logs_d, lean_d = pathlib.Path(logs_d), pathlib.Path(lean_d)
    # modules built by each job (multi-module jobs print "== <module>")
    built = {}
    for j in jobs:
        f = logs_d / (j["job"] + ".log")
        mods = re.findall(r"^== (\S+)", f.read_text(errors="replace"), re.M) if f.exists() else []
        built[j["job"]] = mods
    # per-module runs with end times (from cost.py's job rows: one module per lake job; segments of multi jobs)
    runs = {}
    for j in jobs:
        end = ts(j["start_utc"]) + datetime.timedelta(seconds=j["gate_s"])
        mods = [j["module"]] if j.get("module") else []
        log = (logs_d / (j["job"] + ".log"))
        txt = log.read_text(errors="replace") if log.exists() else ""
        if built[j["job"]]:
            segs = re.split(r"^== (\S+)\n", txt, flags=re.M)
            for m, body in zip(segs[1::2], segs[2::2]):
                runs.setdefault(m, []).append((end, "error: build failed" not in body.split("\n== ")[0]))
        elif mods and j["class"] == "build":
            runs.setdefault(mods[0], []).append((end, j["exit"] == 0))
    # events
    evs = []
    for f in sorted(pathlib.Path(ev_d).glob("opus-events*.jsonl")):
        for line in open(f):
            try:
                e = json.loads(line)
            except ValueError:
                continue
            m = e.get("message")
            if not isinstance(m, dict) or not isinstance(m.get("content"), list) or not e.get("timestamp"):
                continue
            for c in m["content"]:
                if isinstance(c, dict) and c.get("type") == "tool_use":
                    evs.append((ts(e["timestamp"]), c.get("name"), json.dumps(c.get("input", {}))))
    evs.sort()
    out = {"schema": 1, "stage": "S0 (NEXT-PLAN after MS1): baseline only, no target derived",
           "inputs": {"cost": str(cost_p), "logs": str(logs_d), "events": str(ev_d), "lean": str(lean_d)},
           "definitions": __doc__.split("Definitions (also written into the output):\n")[1].split("Python 3")[0],
           "not_attributed": NOT_ATTRIBUTED, "units": {}}
    owner = {}
    for u, spec in UNITS.items():
        for m in spec["modules"]:
            owner.setdefault(m, []).append(u)
    for u, spec in UNITS.items():
        mods = spec["modules"]
        row = {"modules": mods, "note": spec.get("note", ""), "shared_modules": [m for m in mods if len(owner[m]) > 1],
               "lake_runs": 0, "failed_runs": 0, "probes": 0, "gate_s_module_jobs": 0.0, "peak_rss_gib": 0.0,
               "memcap_kills": 0, "modules_without_cost_row": []}
        for m in mods:
            r = pm.get(m)
            if not r:
                row["modules_without_cost_row"].append(m)
                continue
            row["lake_runs"] += r["runs"]
            row["failed_runs"] += r["failed_runs"]
            row["probes"] += r["probes"]
            row["gate_s_module_jobs"] = round(row["gate_s_module_jobs"] + r["gate_s"], 1)
            row["peak_rss_gib"] = max(row["peak_rss_gib"], r["peak_rss_gib"])
            row["memcap_kills"] += r["memcap_kills"]
        mj = [j for j in jobs if set(built[j["job"]]) & set(mods)]
        row["multi_module_jobs"] = [{"job": j["job"], "gate_s": j["gate_s"], "class": j["class"]} for j in mj]
        row["multi_module_jobs_gate_s"] = round(sum(j["gate_s"] for j in mj), 1)
        files = [lean_d / (m.replace(".", "/") + ".lean") for m in mods]
        present = [f for f in files if f.exists()]
        row["files_not_in_tree"] = [str(f.relative_to(lean_d)) for f in files if not f.exists()]
        row["proof_lines"] = sum(len(f.read_text().split("\n")) for f in present)
        row["code_lines"] = sum(code_lines(f.read_text()) for f in present)
        rel = [str(f.relative_to(lean_d)) for f in files]
        wr = re.compile(r"(>|open\(|sed -i|\bcp\b|\bmv\b|write)")
        first = None
        for t, name, inp in evs:
            hit = any(r in inp for r in rel)
            if hit and (name in ("Write", "Edit") or (name == "Bash" and wr.search(inp))):
                first = t
                break
        acc, acc1 = [], []
        for m in mods:
            rs = sorted(runs.get(m, []))
            if not rs:
                continue
            last_fail = max((i for i, (_, ok) in enumerate(rs) if not ok), default=-1)
            okk = [t for i, (t, ok) in enumerate(rs) if ok and i > last_fail]
            if okk:
                acc.append(okk[0])
            ok1 = [t for t, ok in rs if ok]
            if ok1:
                acc1.append(ok1[0])
        row["first_edit_utc"] = first.strftime("%Y-%m-%dT%H:%M:%SZ") if first else None
        row["accept_utc"] = max(acc).strftime("%Y-%m-%dT%H:%M:%SZ") if acc else None
        row["wall_clock_s"] = round((max(acc) - first).total_seconds()) if first and acc else None
        row["first_accept_utc"] = max(acc1).strftime("%Y-%m-%dT%H:%M:%SZ") if acc1 else None
        row["wall_clock_first_accept_s"] = round((max(acc1) - first).total_seconds()) if first and acc1 else None
        out["units"][u] = row
    out["not_measured"] = [
        "agent thinking time inside a span (the span includes other units of the same session)",
        "edits made by Bash commands whose text does not name the file path (then first_edit_utc is later than the true first edit)",
        "probe files that were not committed (E2e.ProbeW, E2e.ProbeWW, E2eAd.ProbeAd): their gate cost is counted, their lines are not",
        "gate time of multi-module and negative jobs per module (listed per job, not split)",
        "time of session 1 before the gate log existed (none: every Lean step ran through the gate)"]
    json.dump(out, open(out_p, "w"), indent=1)
    for u, r in out["units"].items():
        print(u, r["lake_runs"], r["failed_runs"], r["probes"], r["gate_s_module_jobs"], r["multi_module_jobs_gate_s"],
              r["peak_rss_gib"], r["memcap_kills"], r["proof_lines"], r["code_lines"], r["first_edit_utc"],
              r["accept_utc"], r["wall_clock_s"], r["first_accept_utc"], r["wall_clock_first_accept_s"])
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))
