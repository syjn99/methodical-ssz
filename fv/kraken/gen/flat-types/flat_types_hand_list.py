"""Add the names of the types of `HAND_LIST_TYPES` below to their hand lists in gen/axioms-lists/.

usage (cwd fv/kraken):
  python3 -I gen/flat-types/flat_types_hand_list.py <dump.tsv> gen/axioms-lists <module list>

The hand list of a type is <dir>/<type>.lean, with the Go type name in kebab case (for example deposit-request.lean).
The tool makes the file when it does not exist.
Names: every declaration of the dump that matches the pattern `PATTERN` below for the type, and that the file does not
hold yet. They go to the end of the file as `#print axioms` lines.
Imports: every module of <module list> (names separated by white space) under `Prysm.<GoTypeName>.` that the file does
not import yet. They go after the last import line."""
import os, re, sys
dump, out_dir, module_list = sys.argv[1:4]
HAND_LIST_TYPES = ['DepositRequest', 'BuilderDepositRequest', 'BeaconBlocksByRangeRequest', 'BlobSidecarsByRangeRequest',
         'ExecutionPayloadEnvelopesByRangeRequest', 'PartialDataColumnGroupID', 'ValidatorIdentity', 'BuilderPreferences']
# the declarations that the tools of gen/flat-types/ and the generator runs of a type write
PATTERN = (r'^Prysm\.%s\.(Decode\.(generated_|accept_spec$|reject_size_spec$|reject_complete$)|Encode\.generated_|'
           r'Witness\.Generated|SszValue\b|desc\b|desc_|checker|Code\.)')


def kebab(s):
    s = re.sub(r'(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])', '-', s)
    return re.sub(r'[^a-z0-9]+', '-', s.replace('_', '-').lower()).strip('-')


dump_names = [l.split('\t')[0] for l in open(dump) if not l.startswith('#')]
modules = sorted(m for m in open(module_list).read().split() if m)
for t in HAND_LIST_TYPES:
    path = os.path.join(out_dir, f'{kebab(t)}.lean')
    s = open(path).read() if os.path.exists(path) else (
        f'/-! Hand list of the `{t}` declarations for `gen/checks/axioms_gate.py`.\n'
        'Each name must be in the declaration dump and use only the standard axioms. -/\n')
    names = sorted({n for n in dump_names if re.match(PATTERN % t, n)})
    have = set(re.findall(r'^#print axioms (\S+)$', s, re.M))
    new = [n for n in names if n not in have]
    lines = s.split('\n')
    last = max((i for i, l in enumerate(lines) if l.startswith('import ')), default=-1)
    imps = [f'import {m}' for m in modules if m.startswith(f'Prysm.{t}.') and f'import {m}' not in lines]
    if last == -1 and imps:
        imps.append('')
    lines = lines[:last + 1] + imps + lines[last + 1:]
    open(path, 'w').write('\n'.join(lines).rstrip('\n') + '\n' + ''.join(f'#print axioms {n}\n' for n in new))
    print(path, len(imps), 'imports', len(new), 'names')
