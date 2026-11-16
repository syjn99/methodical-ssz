"""Regeneration comparison: run the Python generators of the Lean files on a copy of the tree, and compare each output
with the tracked file. No Lean, no Go, no build.

usage (from the repository root):
  python3 -I -B fv/kraken/gen/checks/regenerate_and_compare.py <work dir> > <result.txt>

  <work dir>   scratch directory. It must not exist. Delete it later with `trash`.

The tree is not changed: every generator runs in a copy of fv/ under <work dir>/copy.
Each output line is `<EQ|DIF|MIS>` TAB generator TAB tracked file TAB detail.
EQ: the output equals the tracked file. DIF: it differs (the detail shows the first changed lines).
MIS: the tracked file does not exist.

To check a change, run it before and after the change and compare the two results with `diff`.
A difference needs a reason.

The script knows these generators and their output names: gen/generator/gen.sh,
the generators of gen/flat-types/, desc_to_lean, list_desc_to_lean, layout and attestation_data_layout.
Section 1 compares every Lean file that gen/generator/gen.sh writes. Sections 2 and 3 name the outputs by their paths in
lean/Prysm/<GoTypeName>/. Section 4 finds its outputs by their headers.
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


# 1. gen/generator/gen.sh, in place in the copy. Every Lean file that the run writes (a new size or modification time) is
#    compared with the tracked file of the same path.
gen_sh = os.path.join(COPY_KRAKEN, 'gen/generator/gen.sh')


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

# 2. The generator run of the flat types (the committed outputs only).
run_generators = open(os.path.join(COPY_KRAKEN, 'gen/flat-types/run_generators.sh')).read()
rows = [l.split() for l in run_generators.split("<<'TYPES'\n")[1].split('TYPES')[0].strip().split('\n')]
NORM = 'prysm/go1.26.10/link-set/norm'
for kind, go_type in rows:
    PK = ('github.com_OffchainLabs_prysm_v7_proto_engine_v1' if kind == 'v1'
          else 'github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1')
    for g, meth, suf, tag in (('decoder', 'UnmarshalSSZ', 'Dec', '--whole-accept'), ('encoder', 'MarshalSSZTo', 'Enc', '--fast-path')):
        tr = os.path.join(KRAKEN, 'lean/Prysm', go_type,
                          'GeneratedDecodeAccept.lean' if g == 'decoder' else 'GeneratedEncodeFastPath.lean')
        if not os.path.exists(tr):
            continue
        cmd = ['python3', '-I', '-B', 'gen/generator/generator.py', g, tag, '--assembly', f'{NORM}/{PK}.{go_type}.{meth}.S', '--const',
               'unmarshalSSZ' if g == 'decoder' else 'marshalSSZTo', '--ir', 'prysm/ir/ir-mainnet.json', '--type',
               f'{kind}.{go_type}', '--prefix', 'Decode.generated' if g == 'decoder' else 'Encode.generated', '--imports',
               f'Prysm.{go_type}.Code', '--open', f'Prysm.{go_type}.Code',
               '--summary', os.path.join(work, f'{go_type}.{tag[2:]}.summary.json')]
        r = run(cmd, COPY_KRAKEN)
        cmp('flat-type run rc=%d' % r.returncode, tr, r.stdout)

# 3. The specification, witness and negative case generators of the flat types (gen/flat-types/).
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
neg_out = os.path.join(work, 'negative-cases-flat-types.json')
r = run(['python3', '-I', '-B', f'{TOOLS}/flat_types_negative_cases.py', 'lean', neg_out], COPY_KRAKEN)
cmp(f'flat_types_negative_cases rc={r.returncode}', os.path.join(KRAKEN, 'gen/checks/negative-cases/negative-cases-flat-types.json'),
    open(neg_out, 'rb').read() if os.path.exists(neg_out) else None)

# 4. desc_to_lean, list_desc_to_lean, layout and attestation_data_layout: found by the "Generated by" header of every SpecChecker.lean and
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
