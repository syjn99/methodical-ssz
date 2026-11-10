#!/usr/bin/env python3
"""Scalability stage S1-S2 template cost (INBOX 011 item 4), from the gate records and job logs only.

Usage: tcost.py <records.jsonl> <logs-dir> <first-job-number> <session-start-utc> <out.json> <last-job-number>
- Jobs: `exit` records of stream `prysm-e2e` whose log is `<logs-dir>/NN-*.log` with
  first-job-number <= NN <= last-job-number (audit AU-16: explicit upper bound, written to "source").
- Per-module gate_s is the CUMULATIVE gate seconds of all attempts, not a build time.
- Kind from the log stem `NN-<kind>[-<target>]`: `lake` + target `E2eScal.X` -> module run of E2eScal.X
  (failed if exit != 0); `scalgen` -> generator run; anything else -> `other`.
- Jobs killed before they ran (foreground timeout while waiting for the gate) have no exit record;
  they are counted from logs/INDEX.md lines containing "child never ran".
- Gate seconds = end_mono - start_mono; peak = max peak_process_rss of the log's MEMCAP lines; memcap kill =
  `killed=True` or exit 125.
- Lines: of the lemma files (E2eScal/Seg, P1, P2Dec, P2Enc), the in-sample files (P1Slot, P2DecAd, P2EncCp),
  the generated files (Gen*) and the generator (gen/scal/*.py); `code` = without blank and `--` lines and
  without `/- ... -/` blocks.
- Agent wall-clock: session-start-utc (the INBOX 011 acknowledgement) to the end of the last counted job.
This is template cost (S1+S2); it is reported separately from any hold-out cost. Python 3 stdlib only.
"""
import datetime, json, pathlib, re, sys

MEM = re.compile(r"peak_process_rss=(\d+)")
K = pathlib.Path(__file__).resolve().parents[2]
LEMMA = ["Seg", "P1", "P2Dec", "P2Enc"]
INSAMPLE = ["P1Slot", "P2DecAd", "P2EncCp"]


def lines(p):
    t = p.read_text().split("\n")
    code, blk = 0, False
    for l in t:
        s = l.strip()
        if blk:
            if "-/" in s:
                blk = False
            continue
        if s.startswith("/-"):
            blk = "-/" not in s[2:]
            continue
        if s and not s.startswith("--"):
            code += 1
    return {"lines": len(t) - (1 if t and t[-1] == "" else 0), "code_lines": code}


def utc(s):
    return datetime.datetime.strptime(s[:19], "%Y-%m-%dT%H:%M:%S")


def main(records, logs, first, start, out, lastj):
    logs = pathlib.Path(logs)
    jobs = []
    for line in open(records):
        r = json.loads(line)
        if r.get("event") != "exit" or r.get("stream") != "prysm-e2e":
            continue
        lp = pathlib.Path(r.get("log") or "")
        if lp.parent != logs:
            continue
        m = re.match(r"(\d+)-([a-z0-9]+)(?:-(.*))?$", lp.stem)
        if not m or int(m.group(1)) < first or int(m.group(1)) > lastj:
            continue
        text = lp.read_text(errors="replace") if lp.exists() else ""
        pk = [int(x) for x in MEM.findall(text)]
        jobs.append({"job": lp.stem, "kind": m.group(2), "target": m.group(3), "exit": r["exit_code"],
                     "gate_s": round(r["end_mono"] - r["start_mono"], 1), "end_utc": r["end_utc"],
                     "peak_rss": max(pk) if pk else None,
                     "memcap_kill": "killed=True" in text or r["exit_code"] == 125})
    never = [l.strip() for l in (logs / "INDEX.md").read_text().split("\n")
             if "child never ran" in l and re.match(r"- (\d+)-", l)
             and first <= int(re.match(r"- (\d+)-", l).group(1)) <= lastj]
    mods = {}
    for j in jobs:
        if j["kind"] == "lake" and (j["target"] or "").startswith("E2eScal."):
            d = mods.setdefault(j["target"], {"runs": 0, "failed_runs": 0, "gate_s": 0.0, "peak_rss_bytes": 0,
                                              "memcap_kills": 0, "jobs": []})
            d["runs"] += 1; d["failed_runs"] += j["exit"] != 0; d["gate_s"] = round(d["gate_s"] + j["gate_s"], 1)
            d["peak_rss_bytes"] = max(d["peak_rss_bytes"], j["peak_rss"] or 0); d["memcap_kills"] += j["memcap_kill"]
            d["jobs"].append(j["job"])
    for d in mods.values():
        d["peak_rss_gib"] = round(d["peak_rss_bytes"] / 2 ** 30, 2)
    gen = [j for j in jobs if j["kind"] == "scalgen"]
    lake = [j for j in jobs if j["kind"] == "lake"]
    L = K / "lean/E2eScal"
    files = {f"E2eScal/{n}.lean": lines(L / f"{n}.lean") for n in LEMMA + INSAMPLE if (L / f"{n}.lean").exists()}
    gfiles = {f"E2eScal/{p.name}": lines(p) for p in sorted(L.glob("Gen*.lean"))}
    pyf = {f"gen/scal/{p.name}": lines(p) for p in sorted((K / "gen/scal").glob("*.py"))}
    last = max((utc(j["end_utc"]) for j in jobs), default=utc(start))
    res = {
        "schema": 1,
        "stage": "S1-S2 template cost (INBOX 011, session 6); not hold-out cost",
        "source": {"records": records, "logs": str(logs), "first_job": first, "last_job_bound": lastj},
        "totals": {
            "jobs": len(jobs), "gate_s": round(sum(j["gate_s"] for j in jobs), 1),
            "lake_runs": len(lake), "failed_lake_runs": sum(j["exit"] != 0 for j in lake),
            "generator_runs": len(gen), "failed_generator_runs": sum(j["exit"] != 0 for j in gen),
            "jobs_killed_before_run": len(never),
            "peak_rss_gib": round(max((j["peak_rss"] or 0) for j in jobs) / 2 ** 30, 2) if jobs else 0,
            "memcap_kills": sum(j["memcap_kill"] for j in jobs),
        },
        "agent_wall_clock": {"start_utc": start, "last_job_end_utc": last.strftime("%Y-%m-%dT%H:%M:%SZ"),
                             "seconds": int((last - utc(start)).total_seconds())},
        "per_module": mods,
        "lines": {"lemma": files and {k: v for k, v in files.items() if k.split("/")[1][:-5] in LEMMA},
                  "in_sample": {k: v for k, v in files.items() if k.split("/")[1][:-5] in INSAMPLE},
                  "generated": gfiles, "generator": pyf},
        "jobs_killed_before_run": never,
        "jobs": jobs,
        "note": "Lemma counts are not evidence. The in-sample files re-derive existing hand theorems with the same "
                "statement; their cost is template cost. Gate seconds exclude time spent waiting for the gate. "
                "Per-module gate_s is cumulative over all attempts, not a cold build time.",
    }
    pathlib.Path(out).write_text(json.dumps(res, indent=1) + "\n")
    t = res["totals"]
    print(f"jobs {t['jobs']} lake {t['lake_runs']} failed {t['failed_lake_runs']} gate {t['gate_s']} s "
          f"peak {t['peak_rss_gib']} GiB kills {t['memcap_kills']} wall {res['agent_wall_clock']['seconds']} s")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5], int(sys.argv[6]))
