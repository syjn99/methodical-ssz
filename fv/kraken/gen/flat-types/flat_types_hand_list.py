"""Add the names of the types of the rows of gen/generator/types.tsv with the companion `hand-list` to their hand
lists in gen/axioms-lists/.

usage (cwd fv/kraken):
  python3 -I gen/flat-types/flat_types_hand_list.py <dump.tsv> gen/axioms-lists <module list>

The hand list of a type is <dir>/<type>.lean, with the Go type name in kebab case (for example deposit-request.lean).
The tool makes the file when it does not exist.
Names: every declaration of the dump that matches the pattern `PATTERN` below for the type, and that the file does not
hold yet. They go to the end of the file as `#print axioms` lines.
Remove each `#print axioms` line whose name matches `PATTERN` and is not in the dump.
Lean can rename auxiliary declarations, for example `._proof_1_2`.
Imports: every module of <module list> (names separated by white space) under `Prysm.<GoTypeName>.` that the file does
not import yet. They go after the last import line."""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'generator'))
import types_table  # noqa: E402
from types_table import kebab  # noqa: E402
dump, out_dir, module_list = sys.argv[1:4]
# the declarations that the tools of gen/flat-types/ and the generator runs of a type write
PATTERN = (r'^Prysm\.%s\.(Decode\.(generated_|accept_spec$|reject_size_spec$|reject_complete$)|Encode\.generated_|'
           r'Witness\.Generated|SszValue\b|desc\b|desc_|checker|Code\.)')


dump_names = [l.split('\t')[0] for l in open(dump) if not l.startswith('#')]
modules = sorted(m for m in open(module_list).read().split() if m)
for t in types_table.types_with('hand-list'):
    path = os.path.join(out_dir, f'{kebab(t)}.lean')
    s = open(path).read() if os.path.exists(path) else (
        f'/-! Hand list of the `{t}` declarations for `gen/checks/axioms_gate.py`.\n'
        'Each name must be in the declaration dump and use only the standard axioms. -/\n')
    names = sorted({n for n in dump_names if re.match(PATTERN % t, n)})
    dump_set = set(dump_names)
    lines = [l for l in s.split('\n') if not ((m := re.match(r'#print axioms (\S+)$', l))
                                               and re.match(PATTERN % t, m.group(1)) and m.group(1) not in dump_set)]
    gone = len(s.split('\n')) - len(lines)
    have = set(re.findall(r'^#print axioms (\S+)$', '\n'.join(lines), re.M))
    new = [n for n in names if n not in have]
    last = max((i for i, l in enumerate(lines) if l.startswith('import ')), default=-1)
    imps = [f'import {m}' for m in modules if m.startswith(f'Prysm.{t}.') and f'import {m}' not in lines]
    if last == -1 and imps:
        imps.append('')
    lines = lines[:last + 1] + imps + lines[last + 1:]
    open(path, 'w').write('\n'.join(lines).rstrip('\n') + '\n' + ''.join(f'#print axioms {n}\n' for n in new))
    print(path, len(imps), 'imports', len(new), 'names', gone, 'removed')
