"""Evidence tool (not part of gen/scal): write <dir>/Prysm/<GoTypeName>/DecodeSpec.lean from the generated accept
statement text of <dir>/Prysm/<GoTypeName>/GeneratedDecodeAccept.lean (statement copied, input chunks replaced by the encoding of the EthLib-decoded value): the
text of the script `mkspeck.py` generalised to n fields of uint64 / byte vectors.
usage: python3 -I -B f24speck.py <fv/kraken/lean> [X ...]"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from f24spec import T, GO_TYPE, new_names  # noqa: E402

DEC = ['Dpr', 'Bdr', 'Bbr', 'Bsr', 'Epr', 'Pdc', 'Vid']


def emit(d, X):
    ty, fs, chk = T[X]
    x = X.lower()
    P, pe = f'P{X}', f'p{x}Enc'
    N = sum(f[2] for f in fs)
    n = len(fs)
    src = open(os.path.join(d, 'Prysm', GO_TYPE[X], 'GeneratedDecodeAccept.lean')).read()
    i = src.index('theorem Decode.generated_accept : ∀ ')
    j = src.index(' := by\n', i)
    stmt = src[i + len('theorem Decode.generated_accept : '):j]
    intro = re.search(r'\n  intro (k hk hf [^\n]*)\n', src[j:]).group(1).split()
    ex = [f'(uintBytes 8 g.{f[0]}.toNat).toList' if f[1] == 'u' else f'g.{f[0]}.toArray.toList' for f in fs]
    lp = ['(by simp [Spec.uintBytes_size])' if f[1] == 'u' else '(by simp)' for f in fs]
    fvs = ' '.join(f'fv{k}' for k in range(n))
    hyps = ' '.join(rf'\(hfv{k} : fv{k}\.length = \d+\)' for k in range(n))
    line = re.search(rf'\n    \({fvs} : List UInt8\) {hyps}\n', stmt)
    assert line, X
    stmt = stmt.replace(line.group(0), f'\n    (bsA : Array UInt8) (v : Value) (hd : deserialize prysm{X}Desc bsA = .ok v)\n', 1)
    assert stmt.count('(h_mem : s.dmem =⋆') == 1
    stmt = stmt.replace('(h_mem : s.dmem =⋆', f'(Pm : ∀ g : {P}, bsA = {pe} g →\n      s.dmem =⋆', 1)
    assert stmt.count(f'(hlen : s.regs.rcx = {N})') == 1, X
    stmt = stmt.replace(f'(hlen : s.regs.rcx = {N})', '(hlen : s.regs.rcx.toNat = bsA.size)', 1)
    assert stmt.count(',\n    Eventually (step1 Host.exe)') == 1
    stmt = stmt.replace(',\n    Eventually (step1 Host.exe)',
                        f',\n    ∃ g : {P}, g.toValue = v ∧ bsA = {pe} g ∧\n    Eventually (step1 Host.exe)', 1)
    for k in range(n):
        stmt = re.sub(rf'\bfv{k}\b', ex[k], stmt)
    assert not re.search(r'\bfv\d\b', stmt)
    fvn = [f'fv{k}' for k in range(n)]
    hfn = [f'hfv{k}' for k in range(n)]
    names = [y for y in intro if y not in fvn + hfn]
    k_fv = intro.index('fv0')
    names_i = names[:k_fv] + ['bsA', 'v', 'hd'] + names[k_fv:]
    names_i = ['Pm' if y == 'h_mem' else y for y in names_i]
    args = []
    for y in intro:
        if y in fvn:
            args.append('_')
        elif y in hfn:
            args.append(lp[hfn.index(y)])
        elif y == 'h_mem':
            args.append('(Pm g hb)')
        elif y == 'hlen':
            args.append('hn')
        else:
            args.append(y)
    gname = f'E2eScal.Gen.{x}_g5dec_accept'
    return f'''import E2eScal.Gen5F24{X}Dec
import E2eScal.F24{X}Spec

/-!
# Spec alignment of the real `{ty}` decoder (FLAT24 / H7)

Built on the GENERATED theorems of `Gen5F24{X}Dec.lean` (`p2dec --gen5`, one-shot run of FLAT24 Part 1; raw output, not
edited):
- `{x}_e2e_accept_spec_k`: if EthLib accepts `bsA` (`prysm{X}Desc`) as `v`, there is `g : {P}` with `g.toValue = v`
  and `bsA = {pe} g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
  The statement is the generated accept statement (kind instance) with the input chunks replaced by the
  encoding of `g` (text written by the FLAT24 evidence script `f24speck.py` from the generated statement; then checked
  by Lean against `{gname}`).
- `{x}_e2e_reject_size_spec`: `bs.size ≠ {N}` → EthLib rejects, and the machine code returns `ssz.ErrSize`
  (generated `{x}_g5dec_reject`).
- `{x}_e2e_reject_complete`: every input that EthLib rejects has `size ≠ {N}` (the path condition of the size reject).
Not stated here: that the callee error paths (`fmt.errorf` wraps) are unreachable when `size = {N}`.
-/

open Machine Runtime TestTarget Codec Prysm.{GO_TYPE[X]}.Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.F24

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept side: the generated accept statement for the input chunks of the `g` that EthLib decodes. -/
theorem {x}_e2e_accept_spec_k : {stmt} := by
  intro {' '.join(names_i)}
  obtain ⟨g, rfl, hb⟩ := p{x}_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have hn : s.regs.rcx = {N} := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, p{x}_enc_size]; rfl
  exact {gname} {' '.join(args)}

/-- `len(buf) ≠ {N}`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem {x}_e2e_reject_size_spec (k : Nat) (hk : {X}Unmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh {X}Unmarshal k) (bs : Array UInt8) (hbs : bs.size ≠ {N})
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize prysm{X}Desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨p{x}_spec_rejects bs hbs, E2eScal.Gen.{x}_g5dec_reject k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects has `size ≠ {N}`: the path condition of the size reject.
(The callee error returns are not covered.) -/
theorem {x}_e2e_reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize prysm{X}Desc bs = .ok v) :
    bs.size ≠ {N} := fun h{N} => h ((p{x}_spec_accepts_iff bs).mpr h{N})

end E2eScal.F24
'''


if __name__ == '__main__':
    d = sys.argv[1]
    for X in (sys.argv[2:] or DEC):
        open(os.path.join(d, 'Prysm', GO_TYPE[X], 'DecodeSpec.lean'), 'w').write(new_names(emit(d, X), X))
        print(X)
