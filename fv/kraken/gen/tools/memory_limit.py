#!/usr/bin/env python3
"""Copy of an earlier memory watchdog (not in this tree; that file is not edited).
Change against the original: a per-process trigger no longer inflates the reported
session peak (it used to set total = cap + 1 and add the other processes); it sets
its own flag and the reported peak_session_rss is the true anonymous session sum.

Run a command in its own session; every 0.1 s sum the
anonymous RSS (RssAnon) of all processes in that session; if the sum exceeds
the cap, or (with --per-proc) one process's full VmRSS exceeds its cap, SIGKILL
the whole session and exit 125. Prints the peaks at the end.

usage: memory_limit.py <cap_bytes> [--per-proc <bytes>] -- cmd args...
       --per-proc: also kill the session when one process exceeds <bytes>
Exit: the child's exit code, or 125 if the cap killed it."""
import os
import signal
import subprocess
import sys
import time

cap = int(sys.argv[1])
args = sys.argv[2:]
pcap = None
if args[0] == "--per-proc":
    pcap = int(args[1]); args = args[2:]
assert args[0] == "--"
cmd = args[1:]
ppeak = 0
ptrig = False
child = subprocess.Popen(cmd, start_new_session=True)
sid = child.pid
peak = 0
killed = False


def session_rss():
    global ppeak, ptrig
    total = 0
    for p in os.listdir("/proc"):
        if not p.isdigit():
            continue
        try:
            with open(f"/proc/{p}/stat") as f:
                st = f.read()
            fields = st[st.rindex(")") + 2:].split()
            if int(fields[3]) != sid:  # session id (field 6 overall)
                continue
            with open(f"/proc/{p}/status") as f:
                for line in f:
                    if line.startswith("VmRSS:"):  # per process: full RSS
                        r1 = int(line.split()[1]) * 1024
                        ppeak = max(ppeak, r1)
                        if pcap is not None and r1 > pcap:
                            ptrig = True
                    elif line.startswith("RssAnon:"):  # session total: anonymous memory
                        total += int(line.split()[1]) * 1024
                        # (shared file pages of mmapped .olean files are counted once per
                        # process in VmRSS; they are page cache, not what the OOM killer frees)
        except (OSError, ValueError, IndexError):
            continue
    return total


while child.poll() is None:
    r = session_rss()
    peak = max(peak, r)
    if r > cap or ptrig:
        killed = True
        try:
            os.killpg(sid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        break
    time.sleep(0.1)
child.wait()
# kill any leftover in the session
try:
    os.killpg(sid, signal.SIGKILL)
except ProcessLookupError:
    pass
print(f"MEMCAP peak_session_rss={peak} bytes ({peak / 2**30:.2f} GiB) cap={cap} peak_process_rss={ppeak} "
      f"({ppeak / 2**30:.2f} GiB) per_proc_cap={pcap} killed={killed} per_proc_trigger={ptrig} child_rc={child.returncode}",
      flush=True)
sys.exit(125 if killed else child.returncode)
