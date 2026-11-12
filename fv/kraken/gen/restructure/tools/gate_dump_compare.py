"""Compare two dumps of the axioms gate across a rename step. No Lean.

usage:
  python3 -I -B fv/kraken/gen/restructure/tools/gate_dump_compare.py <before.tsv> <after.tsv> <map dir>...

  <before.tsv>  the <dump.tsv> of `axioms_gate.py run` on the base tree of the step
  <after.tsv>   the <dump.tsv> of `axioms_gate.py run` on the tree after the step
  <map dir>     the map directories of the steps between the two trees, in order

A dump row is: name, kind, type hash, value hash, axiom set (the format of decl_dump.lean of the skill).
The script maps each old name of <before.tsv> through the declaration rows of the maps.
A name below a declaration row (for example `X._proof_1` below `X`) follows that row.
Then it compares the names that are not internal: each must exist in both dumps, with the same kind and axiom set.
Internal names (a component starts with `_`) can also hold module names, so they are compared as a multiset
of (kind, axiom set). The hashes are not compared, because a rename changes the names in types and values.
Exit 0: no missing name, no extra name, no changed kind or axiom set. Exit 1: a difference. Exit 2: usage.
"""
import collections
import os
import sys

if len(sys.argv) < 4:
    sys.exit(__doc__)
before_path, after_path, map_dirs = sys.argv[1], sys.argv[2], sys.argv[3:]


def read_dump(path):
    rows = {}
    for line in open(path, encoding='utf-8'):
        if line.startswith('#') or not line.strip():
            continue
        name, kind, _type_hash, _value_hash, axioms = line.rstrip('\n').split('\t')
        rows[name] = (kind, axioms)
    return rows


def internal(name):
    return any(c.startswith('_') for c in name.split('.'))


renames = []
for d in map_dirs:
    step = {}
    for line in open(os.path.join(d, 'names.tsv'), encoding='utf-8'):
        c = line.rstrip('\n').split('\t')
        if c[0] == 'declaration':
            step[c[1]] = c[2]
    renames.append(step)


def new_name(name):
    for step in renames:
        if name in step:
            name = step[name]
            continue
        parts = name.split('.')
        for j in range(len(parts) - 1, 0, -1):
            prefix = '.'.join(parts[:j])
            if prefix in step:
                name = step[prefix] + name[len(prefix):]
                break
    return name


before = {new_name(n): v for n, v in read_dump(before_path).items()}
after = read_dump(after_path)
old_public = {n for n in before if not internal(n)}
new_public = {n for n in after if not internal(n)}
missing = sorted(old_public - new_public)
extra = sorted(new_public - old_public)
common = old_public & new_public
changed = sorted(n for n in common if before[n] != after[n])
old_internal = collections.Counter(v for n, v in before.items() if internal(n))
new_internal = collections.Counter(v for n, v in after.items() if internal(n))
print('rows before', len(before), 'after', len(after))
print('missing (not internal)', len(missing), missing[:20])
print('extra (not internal)', len(extra), extra[:20])
print('common', len(common), 'kind or axiom set changed', len(changed), changed[:20])
print('internal before', sum(old_internal.values()), 'after', sum(new_internal.values()),
      'kind and axiom multisets equal', old_internal == new_internal)
sys.exit(0 if not missing and not extra and not changed and old_internal == new_internal else 1)
