"""Evidence tool (not part of gen/generator): write <dir>/Prysm/<GoTypeName>/DecodeSpec.lean from the generated accept
statement text of <dir>/Prysm/<GoTypeName>/GeneratedDecodeAccept.lean (statement copied, input chunks replaced by the encoding of the EthLib-decoded value): the
text of the script `mkspeck.py` generalised to n fields of uint64 / byte vectors.
usage: python3 -I -B flat_types_decode_spec.py <fv/kraken/lean> [GoTypeName ...]"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flat_types_spec import T  # noqa: E402

DEC = ['DepositRequest', 'BuilderDepositRequest', 'BeaconBlocksByRangeRequest', 'BlobSidecarsByRangeRequest', 'ExecutionPayloadEnvelopesByRangeRequest', 'PartialDataColumnGroupID', 'ValidatorIdentity']


def emit(d, X):
    ty, fs, chk = T[X]
    P, pe = 'SszValue', 'SszValue.encode'
    N = sum(f[2] for f in fs)
    n = len(fs)
    src = open(os.path.join(d, 'Prysm', X, 'GeneratedDecodeAccept.lean')).read()
    i = src.index('theorem Decode.generated_accept : ∀ ')
    j = src.index(' := by\n', i)
    statement_text = src[i + len('theorem Decode.generated_accept : '):j]
    intro = re.search(r'\n  intro (k hk hf [^\n]*)\n', src[j:]).group(1).split()
    ex = [f'(uintBytes 8 g.{f[0]}.toNat).toList' if f[1] == 'u' else f'g.{f[0]}.toArray.toList' for f in fs]
    lp = ['(by simp [Spec.uintBytes_size])' if f[1] == 'u' else '(by simp)' for f in fs]
    fvs = ' '.join(f'fv{k}' for k in range(n))
    hyps = ' '.join(rf'\(hfv{k} : fv{k}\.length = \d+\)' for k in range(n))
    line = re.search(rf'\n    \({fvs} : List UInt8\) {hyps}\n', statement_text)
    assert line, X
    statement_text = statement_text.replace(line.group(0), f'\n    (bsA : Array UInt8) (v : Value) (hd : deserialize desc bsA = .ok v)\n', 1)
    assert statement_text.count('(h_mem : s.dmem =⋆') == 1
    statement_text = statement_text.replace('(h_mem : s.dmem =⋆', f'(Pm : ∀ g : {P}, bsA = {pe} g →\n      s.dmem =⋆', 1)
    assert statement_text.count(f'(hlen : s.regs.rcx = {N})') == 1, X
    statement_text = statement_text.replace(f'(hlen : s.regs.rcx = {N})', '(hlen : s.regs.rcx.toNat = bsA.size)', 1)
    assert statement_text.count(',\n    Eventually (step1 Host.exe)') == 1
    statement_text = statement_text.replace(',\n    Eventually (step1 Host.exe)',
                        f',\n    ∃ g : {P}, g.toValue = v ∧ bsA = {pe} g ∧\n    Eventually (step1 Host.exe)', 1)
    for k in range(n):
        statement_text = re.sub(rf'\bfv{k}\b', ex[k], statement_text)
    assert not re.search(r'\bfv\d\b', statement_text)
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
    gname = f'Prysm.{X}.Decode.generated_accept'
    return f'''import Prysm.{X}.GeneratedDecodeAccept
import Prysm.{X}.Spec

/-!
# Spec alignment of the real `{ty}` decoder (24 flat hold-out types)

Built on the GENERATED theorems of `Prysm/{X}/GeneratedDecodeAccept.lean` (`decoder --whole-accept`, one run per type by `run_generators.sh`; raw output, not
edited):
- `Decode.accept_spec`: if EthLib accepts `bsA` (`desc`) as `v`, there is `g : {P}` with `g.toValue = v`
  and `bsA = {pe} g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
  The statement is the generated accept statement (kind instance) with the input chunks replaced by the
  encoding of `g` (text written by the evidence script `flat_types_decode_spec.py` from the generated statement; then checked
  by Lean against `{gname}`).
- `Decode.reject_size_spec`: `bs.size ≠ {N}` → EthLib rejects, and the machine code returns `ssz.ErrSize`
  (generated `Decode.generated_reject`).
- `Decode.reject_complete`: every input that EthLib rejects has `size ≠ {N}` (the path condition of the size reject).
Not stated here: that the callee error paths (`fmt.errorf` wraps) are unreachable when `size = {N}`.
-/

open Machine Runtime Codec Prysm.{X}.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.{X}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept side: the generated accept statement for the input chunks of the `g` that EthLib decodes. -/
theorem Decode.accept_spec : {statement_text} := by
  intro {' '.join(names_i)}
  obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd
  refine ⟨g, rfl, hb, ?_⟩
  have hn : s.regs.rcx = {N} := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, SszValue.encode_size]; rfl
  exact {gname} {' '.join(args)}

/-- `len(buf) ≠ {N}`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem Decode.reject_size_spec (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (bs : Array UInt8) (hbs : bs.size ≠ {N})
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨SszValue.spec_rejects bs hbs, Prysm.{X}.Decode.generated_reject k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects has `size ≠ {N}`: the path condition of the size reject.
(The callee error returns are not covered.) -/
theorem Decode.reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize desc bs = .ok v) :
    bs.size ≠ {N} := fun h{N} => h ((SszValue.spec_accepts_iff bs).mpr h{N})

end Prysm.{X}
'''


if __name__ == '__main__':
    d = sys.argv[1]
    for X in (sys.argv[2:] or DEC):
        open(os.path.join(d, 'Prysm', X, 'DecodeSpec.lean'), 'w').write(emit(d, X))
        print(X)
