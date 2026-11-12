"""FLAT24: write prysm/go1.26.10/e2e/f24/negcases-f24.json (cases for gen/e2e/negative.py).
Per decoder type: spec_k control; mutants of the generated accept theorem (post rax), the generated size-reject
theorem (post rax), spec_k (hlen + 1), the accept witness (post rax). Per encoder type: spec control; mutants of the
generated fast-path theorem (post rax), the spec corollary (hcap weakened by 8), the witness (post rax)."""
import json, os, re, sys
L = sys.argv[1]   # fv/kraken/lean
DEC = ['Dpr', 'Bdr', 'Bbr', 'Bsr', 'Epr', 'Pdc', 'Vid']
ENC = ['Bbr', 'Bdr', 'Bpf', 'Bsr', 'Dpr', 'Epr', 'Pdc', 'Vid']


def stmt_of(path, thm):
    s = open(os.path.join(L, path)).read()
    i = s.index(f'theorem {thm} ')
    j = s.find('\ntheorem ', i + 1)
    for t in ('\nend ', '\nexample', '\n/--', '\ndef '):
        k = s.find(t, i + 1)
        if k != -1 and (j == -1 or k < j):
            j = k
    return s[i:j]


def case(cid, mod, thm, old=None, new=None):
    if old is None:
        return dict(id=cid, module=mod, theorem=thm, kind='control')
    body = stmt_of(mod, thm)
    assert body.count(old) == 1, (cid, body.count(old))
    return dict(id=cid, module=mod, theorem=thm, kind='stmt', old=old, new=new)


C = []
for X in DEC:
    x = X.lower()
    N = int(re.search(r'\(hlen : s\.regs\.rcx = (\d+)\)', stmt_of(f'E2eScal/Gen5F24{X}Dec.lean', f'{x}_g5dec_accept')).group(1))
    C.append(case(f'f24-{x}-speck-control', f'E2eScal/F24{X}SpecK.lean', f'{x}_e2e_accept_spec_k'))
    C.append(case(f'f24-{x}-accept-rax', f'E2eScal/Gen5F24{X}Dec.lean', f'{x}_g5dec_accept',
                  'st.data.regs.rax = 0 ∧', 'st.data.regs.rax = 1 ∧'))
    C.append(case(f'f24-{x}-reject-rax', f'E2eScal/Gen5F24{X}Dec.lean', f'{x}_g5dec_reject',
                  'st.data.regs.rax = e0', 'st.data.regs.rax = e1'))
    C.append(case(f'f24-{x}-speck-hlen', f'E2eScal/F24{X}SpecK.lean', f'{x}_e2e_accept_spec_k',
                  '(hlen : s.regs.rcx.toNat = bsA.size)', '(hlen : s.regs.rcx.toNat = bsA.size + 1)'))
    C.append(case(f'f24-{x}-wita-rax', f'E2eScal/Wit{X}GA.lean', f'{x}_accept_runs',
                  'st.data.regs.rax = 0 ∧', 'st.data.regs.rax = 1 ∧'))
for X in ENC:
    x = X.lower()
    sp = stmt_of(f'E2eScal/E2cSpec{X}.lean', f'{x}_e2c_spec_k')
    n = int(re.search(r'\(hcap : s\.regs\.rcx\.toNat \+ (\d+) ≤ s\.regs\.rdi\.toNat\)', sp).group(1))
    wt = stmt_of(f'E2eScal/WitE2c{X}.lean', f'{x}_e2c_wit_empty')
    rax = re.search(r'st\.data\.regs\.rax = (0x[0-9a-f]+)', wt).group(1)
    C.append(case(f'f24-{x}-espec-control', f'E2eScal/E2cSpec{X}.lean', f'{x}_e2c_spec_k'))
    C.append(case(f'f24-{x}-fast-rax', f'E2eScal/Gen6F24{X}Enc.lean', f'{x}_g6e_fast',
                  'st.data.regs.rax = s.regs.rbx', 'st.data.regs.rax = s.regs.rcx'))
    C.append(case(f'f24-{x}-espec-hcap', f'E2eScal/E2cSpec{X}.lean', f'{x}_e2c_spec_k',
                  f'(hcap : s.regs.rcx.toNat + {n} ≤ s.regs.rdi.toNat)', f'(hcap : s.regs.rcx.toNat + {n - 8} ≤ s.regs.rdi.toNat)'))
    C.append(case(f'f24-{x}-ewit-rax', f'E2eScal/WitE2c{X}.lean', f'{x}_e2c_wit_empty',
                  f'st.data.regs.rax = {rax}', 'st.data.regs.rax = 0x8'))
json.dump(C, open(sys.argv[2], 'w'), indent=1, ensure_ascii=False)
print(len(C), sum(1 for c in C if c['kind'] == 'control'))
