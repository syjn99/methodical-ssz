"""Regeneration comparison: run the Python generators of the Lean files on a copy of the tree, and compare each output
with the tracked file. No Lean, no Go, no build.

usage (from the repository root):
  python3 -I -B fv/kraken/gen/restructure/tools/regen.py <work dir> [--files <files.tsv>]... > <result.txt>

  <work dir>   scratch directory. It must not exist. Delete it later with `trash`.
  --files      a files.tsv of a map. The module names of its rows let the script recognize the imports that the
               generator adds by itself in the hold-out files. Give the files.tsv of the shared-layer map:
               fv/kraken/gen/restructure/maps/shared-layer/files.tsv

The tree is not changed: every generator runs in a copy of fv/ under <work dir>/copy.
Each output line is `<EQ|DIF|MIS|NOT>` TAB generator TAB tracked file TAB detail.
EQ: the output equals the tracked file. DIF: it differs (the detail shows the first changed lines).
MIS: the tracked file does not exist. NOT: the tracked input of a hold-out command is not in the tree.

Run it before and after a step and compare the two results with `diff`.
Expected: the same lines, except that the generator outputs of the moved types can change from DIF to EQ.
The generators that write files of a moved type must reproduce the moved file, or the difference needs a reason.

The script knows the generators and the output names of the tree at the base of the flat-types step
(gen/scal/gen.sh, the hold-out headers of lean/E2eScal/, f24 and e2c tools, descterm, lvdescterm, layout, adlayout).
The flat-types step moves those outputs. Update the paths of sections 1 to 4 in that step.
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


# 1. gen/scal/gen.sh, in place in the copy.
gen_sh = os.path.join(COPY_KRAKEN, 'gen/scal/gen.sh')
text = open(gen_sh).read()
r = run(['sh', gen_sh], COPY_KRAKEN)
outs = set()
for m in re.finditer(r'(?:> |--partial-out )lean/E2eScal/(\S+?)\.lean', text):
    outs.add(m.group(1))
# loop targets of gen.sh: the decoder names in the quoted rows and the Gen6...Enc files
for m in re.finditer(r'"[^"]*\b(Gen[45]\w+Dec)( -| --[^"]*)?"', text):
    outs.add(m.group(1))
scal_dir = os.path.join(COPY_KRAKEN, 'lean/E2eScal')
for f in (os.listdir(scal_dir) if os.path.isdir(scal_dir) else []):
    if f.startswith('Gen6') and f.endswith('Enc.lean') and 'F24' not in f:
        outs.add(f[:-5])
for o in sorted(outs):
    if '$' in o:
        continue
    produced = os.path.join(COPY_KRAKEN, 'lean/E2eScal', o + '.lean')
    cmp('gen.sh rc=%d' % r.returncode, os.path.join(KRAKEN, 'lean/E2eScal', o + '.lean'),
        open(produced, 'rb').read() if os.path.exists(produced) else None)
if r.returncode:
    results.append(('gen.sh', 'stderr', r.stderr.decode()[-400:]))

# 2. Hold-out commands: rebuilt from the header of each file. The generator adds some imports by itself.
#    They are recognized by their names before the shared-layer step (hence --files).
GENERATOR_ADDED = re.compile(r"^E2eScal\.(Kind\w*|CallReg|SegRegZ|SegReg|StepK|CallDec|FieldComp|NopView|AcceptTies|"
                             r"RejectTies|U64RR)$")
HOLD_OUT = ("GenBiDec GenDmDec Gen2DdDecPartial Gen3PcDecPartial Gen3SmDecPartial Gen4H6HsDec Gen4H6PbDec Gen4H6PdDec "
            "Gen4H6SaDec Gen4H6SdDec Gen4H6VbDec Gen4H6VeDec").split()
for f in HOLD_OUT:
    p = os.path.join(KRAKEN, 'lean/E2eScal', f + '.lean')
    if not os.path.exists(p):
        results.append(('holdout', os.path.relpath(p, KRAKEN), 'NOT RUN: the file is not in the tree'))
        continue
    tx = open(p).read()
    imps = re.findall(r"^import (\S+)$", tx, re.M)
    source = re.search(r"Generated by `gen/scal/scalgen.py p2dec` from `([^`]+)`", tx)[1]
    go_type = re.search(r"type `(v1alpha1\.\w+)`", tx)[1]
    m = re.search(r"--gen(\d)", tx[:3000])
    mode = f"--gen{m[1]}" if m else ""
    prefix = re.search(r"\b([a-z0-9]+_(?:g\d)?dec)_", tx)[1]
    const = re.search(r"\b([A-Z][a-z0-9]+Unmarshal)\b", tx)[1]
    opened = re.search(r"^open (?:Fk|Machine Runtime TestTarget) (\S+)", tx, re.M)[1]
    user = [i for i in imps if not GENERATOR_ADDED.match(old_module_of.get(i, i))]
    cmd = ["python3", "-I", "-B", "gen/scal/scalgen.py", "p2dec"] + ([mode] if mode else [])
    out = os.path.join(work, f'holdout.{f}.lean')
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
        tr = os.path.join(KRAKEN, 'lean/E2eScal', f'Gen{tag[-1]}F24{X}{suf}.lean')
        if not os.path.exists(tr):
            continue
        cmd = ['python3', '-I', '-B', 'gen/scal/scalgen.py', g, tag, '--S', f'{NORM}/{PK}.{go_type}.{meth}.S', '--const',
               f'{X}{"Unmarshal" if g == "p2dec" else "Marshal"}', '--ir', 'prysm/ir/ir-mainnet.json', '--type',
               f'{kind}.{go_type}', '--prefix', f'{px}_{"g5dec" if g == "p2dec" else "g6e"}', '--imports',
               'E2eScal.F24Code', '--open', 'E2eScal.F24Code',
               '--summary', os.path.join(work, f'{X}.{tag}.summary.json')]
        r = run(cmd, COPY_KRAKEN)
        cmp('f24 part1 rc=%d' % r.returncode, tr, r.stdout)

# 4. Evidence tools of f24 and e2c.
TOOLS = 'prysm/go1.26.10/e2e/f24/tools'
for name, cmdf, glob in (
        ('f24spec', lambda o: ['python3', '-I', '-B', f'{TOOLS}/f24spec.py', o], r'F24\w+Spec\.lean$'),
        ('f24emitenc', lambda o: ['python3', '-I', '-B', f'{TOOLS}/f24emitenc.py', 'lean', o], r'.*\.lean$'),
        ('e2cemit', lambda o: ['python3', '-I', '-B', 'prysm/go1.26.10/e2e/scal/e2c/e2cemit.py', 'lean', o],
         r'.*\.lean$')):
    o = os.path.join(work, name)
    os.makedirs(o)
    r = run(cmdf(o), COPY_KRAKEN)
    for f in sorted(os.listdir(o)):
        if re.match(glob, f):
            cmp(f'{name} rc={r.returncode}', os.path.join(KRAKEN, 'lean/E2eScal', f), open(os.path.join(o, f), 'rb').read())
o = os.path.join(work, 'f24speck')
os.makedirs(o)
for f in (os.listdir(os.path.join(KRAKEN, 'lean/E2eScal')) if os.path.isdir(os.path.join(KRAKEN, 'lean/E2eScal')) else []):
    if re.match(r'Gen5F24\w+Dec\.lean$', f):
        shutil.copy(os.path.join(KRAKEN, 'lean/E2eScal', f), o)
r = run(['python3', '-I', '-B', f'{TOOLS}/f24speck.py', o], COPY_KRAKEN)
for f in sorted(os.listdir(o)):
    if re.match(r'F24\w+SpecK\.lean$', f):
        cmp(f'f24speck rc={r.returncode}', os.path.join(KRAKEN, 'lean/E2eScal', f), open(os.path.join(o, f), 'rb').read())
r = run(['python3', '-I', '-B', f'{TOOLS}/f24wit.py', '.'], COPY_KRAKEN)
for f in sorted(os.listdir(scal_dir) if os.path.isdir(scal_dir) else []):
    if re.match(r'Wit(Dpr|Bdr|Bbr|Bsr|Epr|Pdc|Vid)G[AR]\.lean$', f):
        cmp(f'f24wit rc={r.returncode}', os.path.join(KRAKEN, 'lean/E2eScal', f), open(os.path.join(scal_dir, f), 'rb').read())
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
