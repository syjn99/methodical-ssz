"""Regeneration comparison: run the Python generators of the Lean files on a copy of the tree, and compare each output
with the tracked file. No Lean, no Go, no build.

usage (from the repository root):
  python3 -I -B fv/kraken/gen/checks/regenerate_and_compare.py <work dir> > <result.txt>

  <work dir>   scratch directory. It must not exist. Delete it later with `trash`.

The tree is not changed: every generator runs in a copy of fv/ under <work dir>/copy.
Each output line is `<EQ|DIF|MIS>` TAB generator TAB tracked file TAB detail.
EQ: the output equals the tracked file. DIF: it differs (the detail shows the first changed lines).
MIS: the tracked file does not exist.
NO-: a tracked GeneratedDecodeAccept.lean or GeneratedEncodeFastPath.lean that no accept row of the type table writes.

To check a change, run it before and after the change and compare the two results with `diff`.
A difference needs a reason.

The script knows these generators and their output names: gen/generator/gen.sh,
the generators of gen/flat-types/, desc_to_lean and layout.
Section 1 compares the output of every accept row of the type table gen/generator/types.tsv.
Section 2 names the outputs by their paths in lean/Prysm/<GoTypeName>/. Section 3 finds its outputs by their headers.
"""
import difflib
import os
import re
import shutil
import subprocess
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'generator'))
import types_table  # noqa: E402

args = sys.argv[1:]
if not args or args[0].startswith('-'):
    sys.exit(__doc__)
if len(args) != 1:
    sys.exit(__doc__)
work = os.path.abspath(args[0])
if os.path.exists(work):
    sys.exit(f'error: {work} exists. Delete it with trash, or give another directory.')
root = subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True, text=True, check=True).stdout.strip()
KRAKEN = os.path.join(root, 'fv/kraken')
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


def lean_stats(d):
    out = {}
    for dp, dn, fs in os.walk(d):
        for f in fs:
            if f.endswith('.lean'):
                st = os.stat(os.path.join(dp, f))
                out[os.path.join(dp, f)] = (st.st_mtime_ns, st.st_size)
    return out


# 1. gen/generator/gen.sh of the copy, with an output directory. The output of each accept row of the type table is
#    compared with the tracked file of the row.
gen_out = os.path.join(work, 'gen-sh')
r = run(['sh', os.path.join(COPY_KRAKEN, 'gen/generator/gen.sh'), gen_out], COPY_KRAKEN)
written = set()
for row in sorted((x for x in types_table.rows() if x['expect'] == 'accept'), key=types_table.output):
    produced = os.path.join(gen_out, f"{row['type']}.{types_table.MODES[row['mode']][2]}.lean")
    written.add(types_table.output(row))
    cmp('gen.sh rc=%d' % r.returncode, os.path.join(KRAKEN, types_table.output(row)),
        open(produced, 'rb').read() if os.path.exists(produced) else None)
for t in sorted(os.listdir(os.path.join(KRAKEN, 'lean/Prysm'))):
    for f in ('GeneratedDecodeAccept.lean', 'GeneratedEncodeFastPath.lean'):
        rel = f'lean/Prysm/{t}/{f}'
        if os.path.exists(os.path.join(KRAKEN, rel)) and rel not in written:
            results.append(('gen.sh', rel, 'NO-ROW: no accept row of gen/generator/types.tsv writes this file'))
if r.returncode:
    results.append(('gen.sh', 'stderr', r.stderr.decode()[-400:]))

# 2. The specification, witness and negative case generators of the flat types (gen/flat-types/).
TOOLS = 'gen/flat-types'
for name, cmdf, glob in (
        ('flat_types_spec', lambda o: ['python3', '-I', '-B', f'{TOOLS}/flat_types_spec.py', o], r'Spec\.lean$'),
        ('flat_types_encode_spec', lambda o: ['python3', '-I', '-B', f'{TOOLS}/flat_types_encode_spec.py', 'lean', o], r'.*\.lean$')):
    o = os.path.join(work, name)
    os.makedirs(o)
    r = run(cmdf(o), COPY_KRAKEN)
    for dp, dn, fs in sorted(os.walk(o)):
        for f in sorted(fs):
            if re.match(glob, f):
                rel = os.path.relpath(os.path.join(dp, f), o)
                cmp(f'{name} rc={r.returncode}', os.path.join(KRAKEN, 'lean', rel),
                    open(os.path.join(dp, f), 'rb').read())
o = os.path.join(work, 'flat_types_decode_spec')
os.makedirs(o)
for t in sorted(os.listdir(os.path.join(KRAKEN, 'lean/Prysm'))):
    src = os.path.join(KRAKEN, 'lean/Prysm', t, 'GeneratedDecodeAccept.lean')
    if os.path.exists(src):
        os.makedirs(os.path.join(o, 'Prysm', t))
        shutil.copy(src, os.path.join(o, 'Prysm', t))
stats_before = lean_stats(o)
r = run(['python3', '-I', '-B', f'{TOOLS}/flat_types_decode_spec.py', o], COPY_KRAKEN)
for produced in sorted(p for p, st in lean_stats(o).items() if stats_before.get(p) != st):
    rel = os.path.relpath(produced, o)
    cmp(f'flat_types_decode_spec rc={r.returncode}', os.path.join(KRAKEN, 'lean', rel), open(produced, 'rb').read())
stats_before = lean_stats(os.path.join(COPY_KRAKEN, 'lean'))
r = run(['python3', '-I', '-B', f'{TOOLS}/flat_types_witness.py', '.'], COPY_KRAKEN)
stats_after = lean_stats(os.path.join(COPY_KRAKEN, 'lean'))
for produced in sorted(p for p in stats_after if stats_before.get(p) != stats_after[p]):
    rel = os.path.relpath(produced, COPY_KRAKEN)
    cmp(f'flat_types_witness rc={r.returncode}', os.path.join(KRAKEN, rel),
        open(produced, 'rb').read())
# The tool writes the files negative-cases-<type>-generated.json. Each output and each tracked file of that name is compared.
neg_out = os.path.join(work, 'flat_types_negative_cases')
os.makedirs(neg_out)
r = run(['python3', '-I', '-B', f'{TOOLS}/flat_types_negative_cases.py', 'lean', neg_out], COPY_KRAKEN)
NEG_DIR = os.path.join(KRAKEN, 'gen/checks/negative-cases')
for f in sorted(set(os.listdir(neg_out)) | {f for f in os.listdir(NEG_DIR) if f.endswith('-generated.json')}):
    produced = os.path.join(neg_out, f)
    cmp(f'flat_types_negative_cases rc={r.returncode}', os.path.join(NEG_DIR, f),
        open(produced, 'rb').read() if os.path.exists(produced) else None)

# 3. desc_to_lean and layout: found by the "Generated by" header of every SpecChecker.lean and
#    Layout.lean file of the tree, so this section follows a move without a change.
for dp, dn, fs in os.walk(os.path.join(KRAKEN, 'lean')):
    if '.lake' in dp:
        continue
    for f in sorted(fs):
        if not (f.endswith('SpecChecker.lean') or f == 'Layout.lean'):
            continue
        p = os.path.join(dp, f)
        tx = open(p).read()
        m = re.search(r'Generated by `(gen/checks/[a-z_]+\.py)` from `([^`]+)`', tx)
        if not m:
            m2 = re.search(r'Generated by `(gen/checks/[a-z_]+\.py)`', tx)
            if not m2:
                continue
            script, source = m2[1], None
        else:
            script, source = m[1], m[2]
        name = re.search(r'^(?:noncomputable )?(?:def|abbrev) (\S+)', tx, re.M)
        if script.endswith('layout.py'):
            r = run(['python3', '-I', script], COPY_KRAKEN)
        else:
            r = run(['python3', '-I', script, source, name[1]], COPY_KRAKEN)
        cmp(f'{os.path.basename(script)} rc={r.returncode}', p, r.stdout)

for label, f, res in results:
    print(f'{res[:3]}\t{label}\t{f}\t{res}')
