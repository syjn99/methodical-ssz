"""Append FLAT24 names to gen/scal/AxiomsScal.lean (imports after the last import; #print axioms lines at the end).
Names: every declaration of the dump whose name lies in a FLAT24 module namespace or carries a FLAT24 prefix."""
import re, sys
dump, axs, lean = sys.argv[1:4]
X = ['Dpr', 'Bdr', 'Bbr', 'Bsr', 'Epr', 'Pdc', 'Vid', 'Bpf']
x = [s.lower() for s in X]
pats = [r'^E2eScal\.F24\.', r'^E2eScal\.F24Code\.', r'^E2eScal\.Wit(%s)G[AR]\.' % '|'.join(X),
        r'^E2eScal\.WitE2c(%s)\.' % '|'.join(X), r'^E2eScal\.Gen\.(%s)_g[45]dec' % '|'.join(x),
        r'^E2eScal\.Gen6Enc\.(%s)_g6e' % '|'.join(x), r'^E2eScal\.E2c\.(%s)_e2c' % '|'.join(x),
        r'^E2e\.prysm(%s)Desc' % '|'.join(X), r'^E2e\.P(%s)\.' % '|'.join(X), r'^E2e\.P(%s)$' % '|'.join(X),
        r'^E2e\.p(%s)(_|Enc)' % '|'.join(x), r'^E2e\.dprChecker']
names = []
for l in open(dump):
    if l.startswith('#'):
        continue
    n = l.split('\t')[0]
    if any(re.match(p, n) for p in pats):
        names.append(n)
names = sorted(set(names))
s = open(axs).read()
have = set(re.findall(r'^#print axioms (\S+)$', s, re.M))
new = [n for n in names if n not in have]
mods = sorted(m for m in open(lean).read().split() if m)
lines = s.split('\n')
last = max(i for i, l in enumerate(lines) if l.startswith('import '))
imps = [f'import {m}' for m in mods if f'import {m}' not in lines]
lines = lines[:last + 1] + imps + lines[last + 1:]
out = '\n'.join(lines).rstrip('\n') + '\n' + ''.join(f'#print axioms {n}\n' for n in new)
open(axs, 'w').write(out)
print(len(imps), 'imports', len(new), 'names')
