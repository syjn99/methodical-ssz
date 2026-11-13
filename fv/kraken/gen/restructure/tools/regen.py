"""Regeneration comparison: run the Python generators of the Lean files on a copy of the tree, and compare each output
with the tracked file. No Lean, no Go, no build.

usage (from the repository root):
  python3 -I -B fv/kraken/gen/restructure/tools/regen.py <work dir> [--files <files.tsv>]... > <result.txt>

  <work dir>   scratch directory. It must not exist. Delete it later with `trash`.
  --files      a files.tsv of a map. The module names of its rows let the script recognize the imports that the
               generator adds by itself in the hold-out files, and the earlier output names of the evidence tools.
               Give the files.tsv of the shared-layer map and of the flat-types map (the two maps that moved
               those modules):
               --files fv/kraken/gen/restructure/maps/shared-layer/files.tsv
               --files fv/kraken/gen/restructure/maps/flat-types/files.tsv

The tree is not changed: every generator runs in a copy of fv/ under <work dir>/copy.
Each output line is `<EQ|DIF|MIS|NOT>` TAB generator TAB tracked file TAB detail.
EQ: the output equals the tracked file. DIF: it differs (the detail shows the first changed lines).
MIS: the tracked file does not exist. NOT: the tracked input of a hold-out command is not in the tree.

Run it before and after a step and compare the two results with `diff`.
Expected: the same lines, except that the generator outputs of the moved types can change from DIF to EQ.
The generators that write files of a moved type must reproduce the moved file, or the difference needs a reason.

The script knows the generators and the output names of the tree after the flat-types step
(gen/scal/gen.sh, the hold-out headers, f24 and e2c tools, descterm, lvdescterm, layout, adlayout).
Section 1 compares every Lean file that gen/scal/gen.sh writes. Sections 2 to 4 name the outputs by their paths in
lean/Prysm/<GoTypeName>/. A tool of section 4 that still writes a file under an earlier name is compared with the
tracked file of that name in the files.tsv of the maps given with --files.
"""
import difflib
import os
import re
import shutil
import subprocess
import sys

args = sys.argv[1:]
if not args or args[0].startswith('-'):
    sys.exit(__doc__)
work = os.path.abspath(args[0])
file_maps = []
rest = args[1:]
while rest:
    if rest[0] == '--files' and len(rest) > 1:
        file_maps.append(rest[1])
        rest = rest[2:]
    else:
        sys.exit(__doc__)
if os.path.exists(work):
    sys.exit(f'error: {work} exists. Delete it with trash, or give another directory.')
root = subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True, text=True, check=True).stdout.strip()
KRAKEN = os.path.join(root, 'fv/kraken')
modules = {}
for ftsv in file_maps:
    for line in open(os.path.join(root, ftsv) if not os.path.isabs(ftsv) else ftsv):
        if line.startswith('#') or not line.strip():
            continue
        old, new = line.split('\t')[:2]
        if old.startswith('fv/kraken/lean/') and old.endswith('.lean') and new.startswith('fv/kraken/lean/'):
            modules[old[15:-5].replace('/', '.')] = new[15:-5].replace('/', '.')
old_module_of = {v: k for k, v in modules.items()}
# earlier file name (base name) of a moved Lean file -> its path relative to fv/kraken
moved_path_of = {}
for ftsv in file_maps:
    for line in open(os.path.join(root, ftsv) if not os.path.isabs(ftsv) else ftsv):
        if line.startswith('#') or not line.strip():
            continue
        old, new = line.split('\t')[:2]
        if old.startswith('fv/kraken/lean/') and old.endswith('.lean'):
            moved_path_of[os.path.basename(old)] = new[len('fv/kraken/'):]
os.makedirs(work)
COPY = os.path.join(work, 'copy')
shutil.copytree(os.path.join(root, 'fv'), os.path.join(COPY, 'fv'), symlinks=True,
                ignore=shutil.ignore_patterns('.lake'))
COPY_KRAKEN = os.path.join(COPY, 'fv/kraken')
results = []


def cmp(label, tracked, data):
    ref = open(tracked, 'rb').read() if os.path.exists(tracked) else None
    if ref == data:
        results.append((label, os.path.relpath(tracked, KRAKEN), 'EQ'))
        return
    if ref is None:
        results.append((label, os.path.relpath(tracked, KRAKEN), 'MISSING-TRACKED'))
        return
    a = ref.decode(errors='replace').split('\n')
    b = (data or b'').decode(errors='replace').split('\n')
    d = [x for x in difflib.unified_diff(a, b, lineterm='', n=0) if x[:1] in '+-' and not x.startswith(('+++', '---'))]
    results.append((label, os.path.relpath(tracked, KRAKEN), f'DIFF {len(d)}: ' + ' || '.join(x[:150] for x in d[:4])))


def run(cmd, cwd, **kw):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, **kw)


# 1. gen/scal/gen.sh, in place in the copy. Every Lean file that the run writes (a new size or modification time) is
#    compared with the tracked file of the same path.
gen_sh = os.path.join(COPY_KRAKEN, 'gen/scal/gen.sh')


def lean_stats(d):
    out = {}
    for dp, dn, fs in os.walk(d):
        for f in fs:
            if f.endswith('.lean'):
                st = os.stat(os.path.join(dp, f))
                out[os.path.join(dp, f)] = (st.st_mtime_ns, st.st_size)
    return out


stats_before = lean_stats(os.path.join(COPY_KRAKEN, 'lean'))
r = run(['sh', gen_sh], COPY_KRAKEN)
stats_after = lean_stats(os.path.join(COPY_KRAKEN, 'lean'))
for produced in sorted(p for p in stats_after if stats_before.get(p) != stats_after[p]):
    rel = os.path.relpath(produced, COPY_KRAKEN)
    cmp('gen.sh rc=%d' % r.returncode, os.path.join(KRAKEN, rel), open(produced, 'rb').read())
if r.returncode:
    results.append(('gen.sh', 'stderr', r.stderr.decode()[-400:]))

# 2. Hold-out commands: rebuilt from the header of each file. The generator adds some imports by itself.
#    They are recognized by their names before the shared-layer step (hence --files).
GENERATOR_ADDED = re.compile(r"^E2eScal\.(Kind\w*|CallReg|SegRegZ|SegReg|StepK|CallDec|FieldComp|NopView|AcceptTies|"
                             r"RejectTies|U64RR)$")
# hold-out file (path under lean/Prysm/) -> the prefix of its generated names (the --prefix of its command)
HOLD_OUT = {'BlobIdentifier/GeneratedDecodeRootFieldSegments': 'Decode.generated_root',
            'DepositMessage/GeneratedDecodeRootFieldSegments': 'Decode.generated_root',
            'Deposit_Data/GeneratedDecodeFieldSegmentsPartial': 'Decode.generated_field',
            'PendingConsolidation/GeneratedDecodeCallSegmentsPartial': 'Decode.generated_call',
            'SyncCommitteeMessage/GeneratedDecodeCallSegmentsPartial': 'Decode.generated_call'}
for t in ('HistoricalSummary', 'PowBlock', 'PendingDeposit', 'SyncAggregatorSelectionData', 'SigningData', 'ValidatorBalance',
          'VoluntaryExit'):
    HOLD_OUT[t + '/GeneratedDecodeSteps'] = 'Decode.generated_step'
for f, prefix in HOLD_OUT.items():
    p = os.path.join(KRAKEN, 'lean/Prysm', f + '.lean')
    if not os.path.exists(p):
        results.append(('holdout', os.path.relpath(p, KRAKEN), 'NOT RUN: the file is not in the tree'))
        continue
    tx = open(p).read()
    imps = re.findall(r"^import (\S+)$", tx, re.M)
    source = re.search(r"Generated by `gen/scal/scalgen.py p2dec` from `([^`]+)`", tx)[1]
    go_type = re.search(r"type `(v1alpha1\.\w+)`", tx)[1]
    m = re.search(r"--gen(\d)", tx[:3000])
    mode = f"--gen{m[1]}" if m else ""
    const = 'unmarshalSSZ'
    opened = re.search(r"^open (?:Fk|Machine Runtime) (\S+)", tx, re.M)[1]
    user = [i for i in imps if not GENERATOR_ADDED.match(old_module_of.get(i, i))]
    cmd = ["python3", "-I", "-B", "gen/scal/scalgen.py", "p2dec"] + ([mode] if mode else [])
    out = os.path.join(work, f'holdout.{f.replace("/", ".")}.lean')
    partial = "PARTIAL OUTPUT" in tx[:600]
    if partial:
        cmd += ["--partial-out", out]
    cmd += ["--S", source, "--const", const, "--ir", "prysm/ir/ir-mainnet.json", "--type", go_type, "--prefix", prefix,
            "--imports", ",".join(user), "--open", opened]
    r = run(cmd, COPY_KRAKEN)
    gen = open(out, 'rb').read() if partial and os.path.exists(out) else r.stdout
    cmp('holdout rc=%d' % r.returncode, p, gen)

# 3. f24 part 1 (the committed outputs only).
part1 = open(os.path.join(COPY_KRAKEN, 'prysm/go1.26.10/e2e/f24/gen/part1.sh')).read()
rows = [l.split() for l in part1.split("<<'TYPES'\n")[1].split('TYPES')[0].strip().split('\n')]
NORM = 'prysm/go1.26.10/e2e/f24/link/norm'
for kind, go_type, px in rows:
    X = px[0].upper() + px[1:]
    PK = ('github.com_OffchainLabs_prysm_v7_proto_engine_v1' if kind == 'v1'
          else 'github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1')
    for g, meth, suf, tag in (('p2dec', 'UnmarshalSSZ', 'Dec', '--gen5'), ('p2enc', 'MarshalSSZTo', 'Enc', '--gen6')):
        tr = os.path.join(KRAKEN, 'lean/Prysm', go_type,
                          'GeneratedDecodeAccept.lean' if g == 'p2dec' else 'GeneratedEncodeFastPath.lean')
        if not os.path.exists(tr):
            continue
        cmd = ['python3', '-I', '-B', 'gen/scal/scalgen.py', g, tag, '--S', f'{NORM}/{PK}.{go_type}.{meth}.S', '--const',
               'unmarshalSSZ' if g == 'p2dec' else 'marshalSSZTo', '--ir', 'prysm/ir/ir-mainnet.json', '--type',
               f'{kind}.{go_type}', '--prefix', 'Decode.generated' if g == 'p2dec' else 'Encode.generated', '--imports',
               f'Prysm.{go_type}.Code', '--open', f'Prysm.{go_type}.Code',
               '--summary', os.path.join(work, f'{X}.{tag}.summary.json')]
        r = run(cmd, COPY_KRAKEN)
        cmp('f24 part1 rc=%d' % r.returncode, tr, r.stdout)

# 4. Evidence tools of f24 and e2c.
TOOLS = 'prysm/go1.26.10/e2e/f24/tools'
for name, cmdf, glob in (
        ('f24spec', lambda o: ['python3', '-I', '-B', f'{TOOLS}/f24spec.py', o], r'Spec\.lean$'),
        ('f24emitenc', lambda o: ['python3', '-I', '-B', f'{TOOLS}/f24emitenc.py', 'lean', o], r'.*\.lean$'),
        ('e2cemit', lambda o: ['python3', '-I', '-B', 'prysm/go1.26.10/e2e/scal/e2c/e2cemit.py', 'lean', o],
         r'.*\.lean$')):
    o = os.path.join(work, name)
    os.makedirs(o)
    r = run(cmdf(o), COPY_KRAKEN)
    for dp, dn, fs in sorted(os.walk(o)):
        for f in sorted(fs):
            if re.match(glob, f):
                rel = os.path.relpath(os.path.join(dp, f), o)
                cmp(f'{name} rc={r.returncode}', os.path.join(KRAKEN, moved_path_of.get(rel, 'lean/' + rel)),
                    open(os.path.join(dp, f), 'rb').read())
o = os.path.join(work, 'f24speck')
os.makedirs(o)
for t in sorted(os.listdir(os.path.join(KRAKEN, 'lean/Prysm'))):
    src = os.path.join(KRAKEN, 'lean/Prysm', t, 'GeneratedDecodeAccept.lean')
    if os.path.exists(src):
        os.makedirs(os.path.join(o, 'Prysm', t))
        shutil.copy(src, os.path.join(o, 'Prysm', t))
stats_before = lean_stats(o)
r = run(['python3', '-I', '-B', f'{TOOLS}/f24speck.py', o], COPY_KRAKEN)
for produced in sorted(p for p, st in lean_stats(o).items() if stats_before.get(p) != st):
    rel = os.path.relpath(produced, o)
    cmp(f'f24speck rc={r.returncode}', os.path.join(KRAKEN, 'lean', rel), open(produced, 'rb').read())
stats_before = lean_stats(os.path.join(COPY_KRAKEN, 'lean'))
r = run(['python3', '-I', '-B', f'{TOOLS}/f24wit.py', '.'], COPY_KRAKEN)
stats_after = lean_stats(os.path.join(COPY_KRAKEN, 'lean'))
for produced in sorted(p for p in stats_after if stats_before.get(p) != stats_after[p]):
    rel = os.path.relpath(produced, COPY_KRAKEN)
    cmp(f'f24wit rc={r.returncode}', os.path.join(KRAKEN, moved_path_of.get(os.path.basename(rel), rel)),
        open(produced, 'rb').read())
neg_out = os.path.join(work, 'negcases-f24.json')
r = run(['python3', '-I', '-B', f'{TOOLS}/f24neg.py', 'lean', neg_out], COPY_KRAKEN)
cmp(f'f24neg rc={r.returncode}', os.path.join(KRAKEN, 'prysm/go1.26.10/e2e/f24/negcases-f24.json'),
    open(neg_out, 'rb').read() if os.path.exists(neg_out) else None)

# 5. descterm, lvdescterm, layout and adlayout: found by the "Generated by" header of every SpecChecker.lean and
#    Layout.lean file of the tree, so this section follows a move without a change.
for dp, dn, fs in os.walk(os.path.join(KRAKEN, 'lean')):
    if '.lake' in dp:
        continue
    for f in sorted(fs):
        if not (f.endswith('SpecChecker.lean') or f == 'Layout.lean'):
            continue
        p = os.path.join(dp, f)
        tx = open(p).read()
        m = re.search(r'Generated by `(gen/e2e/[a-z]+\.py)` from `([^`]+)`', tx)
        if not m:
            m2 = re.search(r'Generated by `(gen/e2e/[a-z]+\.py)`', tx)
            if not m2:
                continue
            script, source = m2[1], None
        else:
            script, source = m[1], m[2]
        name = re.search(r'^(?:noncomputable )?(?:def|abbrev) (\S+)', tx, re.M)
        if script.endswith('layout.py'):
            r = run(['python3', '-I', script], COPY_KRAKEN)
        else:
            real = source
            if not os.path.exists(os.path.join(COPY_KRAKEN, real)):
                # the header can name a directory that differs from the place of the input file
                b = os.path.basename(source)
                found = [os.path.relpath(os.path.join(a, x), COPY_KRAKEN)
                         for a, _, xs in os.walk(os.path.join(COPY_KRAKEN, 'prysm')) for x in xs if x == b]
                real = found[0] if found else source
            r = run(['python3', '-I', script, real, name[1]], COPY_KRAKEN)
        cmp(f'{os.path.basename(script)} rc={r.returncode}', p, r.stdout)

for label, f, res in results:
    print(f'{res[:3]}\t{label}\t{f}\t{res}')
