"""Append the names of the eight types (`TYPES` below) to gen/axioms-lists/flat-fixed-size-types.lean (imports after the last import;
#print axioms lines at the end). Names: every declaration of the dump that matches a pattern of `pats` below."""
import re, sys
dump, axs, lean = sys.argv[1:4]
TYPES = ['DepositRequest', 'BuilderDepositRequest', 'BeaconBlocksByRangeRequest', 'BlobSidecarsByRangeRequest',
         'ExecutionPayloadEnvelopesByRangeRequest', 'PartialDataColumnGroupID', 'ValidatorIdentity', 'BuilderPreferences']
# the declarations that the evidence tools and the generator runs of these types write
pats = [r'^Prysm\.(%s)\.(Decode\.(generated_|accept_spec$|reject_size_spec$|reject_complete$)|Encode\.generated_|'
        r'Witness\.Generated|SszValue\b|desc\b|desc_|checker|Code\.)' % '|'.join(TYPES)]
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
