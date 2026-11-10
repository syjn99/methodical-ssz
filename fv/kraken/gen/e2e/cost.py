#!/usr/bin/env python3
"""prysm-e2e cost record (PROOF-PLAN §4): gate wall-clock, runs, failed runs and peak memory per
Lean module and per theorem, from the gate records and the job logs only.

Usage: cost.py <records.jsonl> <logs-dir> <COST.json>
- Jobs: every `exit` record of stream `prysm-e2e` whose `log` lies in <logs-dir>.
- Job name = log file stem `NN-<kind>[-<target>]`. Kind `lake` + target `E2e.X` -> module E2e.X.
  Kind `probe`: the module from PROBE below. Kind `neg`: negative-suite job. Others: `other`.
- Gate seconds = end_mono - start_mono of the exit record. Peak = max `peak_process_rss` over the
  MEMCAP lines of the log (bytes). Memcap kill = a MEMCAP line with `killed=True` or exit 125.
- Theorem rows use THM (module -> theorems proved in it); the cost of a module is shared by its
  theorems (not divided). Python 3 stdlib only.
"""
import json
import pathlib
import re
import sys

PROBE = {  # probe job stem suffix -> module it diagnosed (from the job labels in logs/INDEX.md)
    "A": "E2e.CpAccept", "C": "E2e.CpAccept", "E": "E2e.CpAccept", "F": "E2e.CpAccept",
    "R": "E2e.CpMarshalR", "ER": "E2e.EpReject", "grow": "E2e.CpMarshalG", "n4": "E2e.GoVal",
}
THM = {
    "E2e.Epoch": ["ep_unmarshal_accept_main"],
    "E2e.WitEp": ["ep_uacc_holds (witness)"],
    "E2e.CpAccept": ["cp_e2e_accept_main", "cp_e2e_accept_tail"],
    "E2e.CpReject": ["cp_e2e_reject_size_main", "cp_e2e_epoch_err_unreachable"],
    "E2e.CpSpecK": ["cp_e2e_accept_spec_k", "cp_e2e_reject_size_spec", "cp_e2e_reject_complete"],
    "E2e.CpMarshal": ["cp_e2e_marshal_main"],
    "E2e.Compose": ["cp_e2e_marshal_decoded_receiver"],
    "E2e.CpMarshalR": ["cp_e2e_marshal_reject_main"],
    "E2e.CpSpecM": ["cp_e2e_marshal_spec_k", "cp_e2e_size_main"],
    "E2e.EpReject": ["ep_unmarshal_reject_len_main", "ep_static_table", "ep_static_addr"],
    "E2e.CpCompose": ["cp_e2e_unmarshal_then_marshal"],
    "E2e.CpMarshalG": ["cp_e2e_marshal_grow_main"],
    "E2e.SpecEq": ["prysmCpDesc_serialize_checker", "prysmCpDesc_deserialize_checker"],
    "E2e.Spec": ["pcp_spec_accepts_iff", "pcp_serialize", "pcp_roundtrip"],
    "E2e.GoVal": ["cp_layout", "cp_after_decode_goValue"],
}
NAME = re.compile(r"^(\d+)-([A-Za-z0-9]+)(?:-(.*))?$")
MEM = re.compile(r"peak_process_rss=(\d+)")


def main(records, logs, out):
    logs = pathlib.Path(logs).resolve()
    jobs = []
    for line in open(records):
        r = json.loads(line)
        if r.get("stream") != "prysm-e2e" or r.get("event") != "exit":
            continue
        lp = pathlib.Path(r["log"]).resolve()
        if lp.parent != logs or not lp.exists():
            continue
        m = NAME.match(lp.stem)
        if not m:
            continue
        num, kind, target = int(m[1]), m[2], m[3] or ""
        text = lp.read_text(errors="replace")
        peaks = [int(x) for x in MEM.findall(text)]
        killed = "killed=True" in text or r["exit_code"] == 125
        if kind == "lake" and target.startswith("E2e."):
            cls, mod = "build", target
        elif kind == "probe":
            cls, mod = "probe", PROBE.get(target)
        elif kind == "neg":
            cls, mod = "negative", None
        else:
            cls, mod = "other", None
        jobs.append({"job": lp.stem, "n": num, "class": cls, "module": mod, "label": r["label"],
                     "exit": r["exit_code"], "gate_s": round(r["end_mono"] - r["start_mono"], 1),
                     "start_utc": r["start_utc"], "peak_rss": max(peaks) if peaks else None,
                     "memcap_kill": killed})
    jobs.sort(key=lambda j: j["n"])
    per_mod = {}
    for j in jobs:
        if not j["module"]:
            continue
        d = per_mod.setdefault(j["module"], {"runs": 0, "failed_runs": 0, "probes": 0, "gate_s": 0.0,
                                             "peak_rss_bytes": 0, "memcap_kills": 0, "jobs": []})
        d["runs"] += j["class"] == "build"
        d["probes"] += j["class"] == "probe"
        d["failed_runs"] += j["class"] == "build" and j["exit"] != 0
        d["gate_s"] = round(d["gate_s"] + j["gate_s"], 1)
        d["peak_rss_bytes"] = max(d["peak_rss_bytes"], j["peak_rss"] or 0)
        d["memcap_kills"] += j["memcap_kill"]
        d["jobs"].append(j["job"])
    for d in per_mod.values():
        d["peak_rss_gib"] = round(d["peak_rss_bytes"] / 2 ** 30, 2)
    per_thm = {}
    for mod, ts in THM.items():
        for t in ts:
            if mod in per_mod:
                d = per_mod[mod]
                per_thm[t] = {"module": mod, "gate_s_module": d["gate_s"], "runs_module": d["runs"],
                              "failed_runs_module": d["failed_runs"], "peak_rss_gib": d["peak_rss_gib"]}
    by = {}
    for j in jobs:
        b = by.setdefault(j["class"], {"jobs": 0, "gate_s": 0.0})
        b["jobs"] += 1
        b["gate_s"] = round(b["gate_s"] + j["gate_s"], 1)
    res = {"schema": 1, "source": {"records": str(records), "logs": str(logs)},
           "note": "gate wall-clock only (excludes the agent's thinking/editing time); module cost is shared by "
                   "the theorems of that module, not divided; witnesses are their own modules (WitCp*, WitEp*)",
           "totals": {"jobs": len(jobs), "gate_s": round(sum(j["gate_s"] for j in jobs), 1),
                      "peak_rss_gib": round(max((j["peak_rss"] or 0) for j in jobs) / 2 ** 30, 2),
                      "memcap_kills": sum(j["memcap_kill"] for j in jobs), "by_class": by},
           "per_module": dict(sorted(per_mod.items())), "per_theorem": per_thm, "jobs": jobs}
    json.dump(res, open(out, "w"), indent=1, ensure_ascii=False)
    print(json.dumps(res["totals"]))
    for m, d in sorted(per_mod.items()):
        print(f"{m:16} runs {d['runs']:3} failed {d['failed_runs']:3} probes {d['probes']} gate {d['gate_s']:7.1f}s "
              f"peak {d['peak_rss_gib']} GiB kills {d['memcap_kills']}")
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))
