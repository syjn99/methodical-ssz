# gen5.py -- `scalgen.py p2dec --gen5`: the whole accept theorem (and the size-reject theorem) of a
# flat fixed-size decoder, emitted from the GEN4 walk (front end) with the statement kinds of the GEN5 lemma unit's hand-over
# (`Codec/Kind/DecodeAcceptAnyFrame.lean`: decHeadKindN, decFieldKindN, decEpiKindN, decAcceptKindN; `Codec/DecodeRejectSizeAnyFrame.lean`: decRejectKindN).
#
# Untrusted generator: every emitted theorem is checked by Lean; every statement has a `_kind` line; the kind
# parameters are recomputed independently from the IR and the `.S` by `kindcheck.py`.
#
# FAIL-CLOSED: `g5_derive` and the renderers raise `G5Refuse` (or any other exception) on every input they do not
# model; `p2dec_gen5` in `scalgen.py` returns a text at ONE place only, after all success flags are set.
# The proof recipes are the ones of the GEN5 lemma unit's hand-over (`Gen5Ex*.lean`).
import re

REGS16 = 'rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15'.split()
LEN = '(Int.toBytes_length 8 _)'
ADDR = '(by simp only [Int64.toBitVec_ofNat] <;> bv_omega)'
ADDR0 = '(by simp only [Int64.toBitVec_ofNat]; exact BitVec.add_zero _)'
RVT = {'rcv': 's.regs.rax.toBitVec', 'bf': 's.regs.rbx.toBitVec', 'zero': '0'}
PRIM = 'github.com_OffchainLabs_prysm_v7_consensus_types_primitives.'
# callee symbol -> (code constant, binder suffix, proved spec theorem); the four proved callees (interface of the GEN5 lemma unit)
G5_CALLEES = {PRIM + 'Slot.UnmarshalSSZ': ('Prysm.AttestationData.Code.slotUnmarshalSSZ', 'S', 'Prysm.Slot.Decode.accept_function_spec_holds'),
              PRIM + 'CommitteeIndex.UnmarshalSSZ': ('Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ', 'C', 'Prysm.CommitteeIndex.Decode.accept_function_spec_holds'),
              PRIM + 'ValidatorIndex.UnmarshalSSZ': ('Prysm.ValidatorIndex.Code.unmarshalSSZ', 'V', 'Prysm.ValidatorIndex.Decode.accept_function_spec_holds'),
              PRIM + 'Epoch.UnmarshalSSZ': ('Prysm.Epoch.Code.unmarshalSSZ', 'E', 'Prysm.Epoch.Decode.accept_function_spec_holds')}
G5_IMPORTS = ['Codec.Kind.DecodeAcceptAnyFrameInstances', 'Codec.FieldFrame', 'Prysm.ValidatorIndex.DecodeAcceptFunctionSpec', 'Prysm.Epoch.DecodeAccept', 'Prysm.Slot.DecodeAccept',
              'Codec.DecoderHeadEpilogue', 'Prysm.BlobIdentifier.DecodeRejectSizeKindInstances']
G5_OPENS = 'Codec'
# the statement kinds of the GEN5 lemma unit's hand-over (kindcheck.py pins their modules)
G5_KINDS = ('decHeadKindN', 'decFieldKindN', 'decEpiKindN', 'decAcceptKindN', 'decRejectKindN')


class G5Refuse(Exception):
    """The generator does not model this input: no accept theorem (exit 2)."""


def refuse(why):
    raise G5Refuse(why)


def destr(var, suf=''):
    return f"  obtain ⟨⟨{', '.join(r + suf for r in REGS16)}⟩, zmms{suf}, flags{suf}, mem{suf}⟩ := {var}\n"


def P(t):  # statement style -> proof style (entry state destructured)
    return t.replace('s.regs.', '')


def soff(o):
    b = 's.regs.rsp.toBitVec'
    return f'({b} + {o})' if o > 0 else (f'({b} - {-o})' if o < 0 else b)


def off(b, o):
    return b if o == 0 else f'({b} + {o})'


def at(o, v):
    return ('at', o, v)


# --------------------------------------------------------------------------------------------- the description

class T:
    """One type: frame facts, field list, boundary states, chain theorem names (the data of the kinds)."""

    def __init__(self, **kw):
        self.__dict__.update(kw)
        self.cs = [n for n, _, _ in self.stack] + (['ast'] if self.st else [])
        for i, f in enumerate(self.fields):
            self.cs += [f'aP{i}', f'aL{i}', f'aC{i}'] if f[1] == 'bytes' else [f'aN{i}']
        self.Sx = None
        if self.rt:
            self.Sx = 'S' if self.rt['x'] == 0 else f"S + {self.rt['x']}"
        lo = [n for n, l, _ in self.stack if l is None]
        self.lo_name = lo[0] if lo else None

    # ---- sizes
    def fsize(self, f): return f[2] if f[1] == 'bytes' else 8
    def heap(self, done): return sum(f[2] for f in self.fields[:done] if f[1] == 'bytes')
    def ssz(self): return sum(self.fsize(f) for f in self.fields)
    def nb(self, done): return sum(1 for f in self.fields[:done] if f[1] == 'bytes')
    def sszoff(self, i): return sum(self.fsize(f) for f in self.fields[:i])
    def gooff(self, i): return (8 if self.st else 0) + sum(24 if f[1] == 'bytes' else 8 for f in self.fields[:i])

    # ---- values / slots
    def vterm(self, v, xs):
        k = v[0]
        if k == 'orig':
            return v[1], ('hlo' if v[1] == self.lo_name else 'h' + v[1])
        if k == 'reg': return f'(Int.toBytes 8 s.regs.{v[1]}.toBitVec.toInt)', LEN
        if k == 'ex': return xs[v[1]], 'h' + xs[v[1]]
        if k == 'ptr': return f'(Int.toBytes 8 p{v[1] + 1}.toInt)', LEN
        if k == 'zero': return '(Int.toBytes 8 (0 : UInt64).toBitVec.toInt)', LEN
        if k == 'ret': return f'(Int.toBytes 8 (Host.addrOf (k + {v[1]})).toBitVec.toInt)', LEN
        refuse(f'gen5: no term for slot value {v}')

    def lo_addr(self): return f"(s.regs.rsp.toBitVec - {self.rt['loB']} - BitVec.ofNat 64 S)"

    def chunk(self, sl, xs):
        v = sl[-1]
        a = self.lo_addr() if sl[0] == 'lo' else soff(sl[1])
        return f'Eq ({self.vterm(v, xs)[0]}.At {a})'

    def vlean(self, v):
        k = v[0]
        if k == 'orig': return f'(.orig {self.cs.index(v[1])})'
        if k == 'reg': return f'(.reg .{v[1]})'
        if k == 'zero': return '.zero'
        if k in ('ex', 'ptr', 'ret'): return f'(.{k} {v[1]})'
        refuse(f'gen5: no slot-language form for {v}')

    def sllean(self, sl):
        if sl[0] == 'lo': return f'.lo {self.vlean(sl[1])}'
        return f".at ({'.up' if sl[1] > 0 else '.dn'} {abs(sl[1])}) {self.vlean(sl[2])}"

    def exlean(self, exs):
        return '[' + ', '.join('.lo' if e == 'lo' else f'.n {e}' for e in exs) + ']'

    def dlean(self, d):
        regs = '[' + ', '.join(f'(.{r}, .{v})' for r, v in d['regs']) + ']'
        stk = '[' + ', '.join(self.sllean(s) for s in d['stk']) + ']'
        return f"⟨{d['pc']}, {d['done']}, {regs},\n      {stk},\n      {self.exlean(d['exs'])}⟩"

    def fieldslean(self):
        return '[' + ', '.join(f'.bytes {f[2]}' if f[1] == 'bytes' else '.u64' for f in self.fields) + ']'

    def layout(self):
        """The `DecLayout` literal (kind parameter `L`), from the derived frame facts."""
        lens = [(self.cs.index(n), l) for n, l, _ in self.stack if l is not None]
        rt = 'none' if not self.rt else (f"some ⟨{'true' if self.rt['hS'] else 'false'}, {self.rt['x']}, "
                                          f"{self.cs.index(self.lo_name)}, {self.rt['loB']}⟩")
        # explicit constructor (field order of `DecLayout`: callees nstk lens pre rt gd st exs post frame)
        return ("(Codec.DecLayout.mk [" + ', '.join(c[0] for c in self.callees) + "] " + str(len(self.stack))
                + "\n      [" + ', '.join(f'({i}, {l})' for i, l in lens) + "]\n      ["
                + ', '.join(self.sllean(s) for s in self.pre) + "]\n      (" + rt + ") " + str(self.gd)
                + " " + ('true' if self.st else 'false') + " " + self.exlean(self.exs)
                + "\n      [" + ', '.join(self.sllean(s) for s in self.post) + "]\n      " + str(self.frame) + ")")

    # ---- memory
    def mem(self, stk, done, xs, ind='      '):
        ch = ['Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)']
        ch += [self.chunk(s, xs) for s in stk]
        ch.append('Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))')
        if self.rt:
            h = self.heap(done)
            ch.append('Heap avail' if h == 0 else f'Heap (avail - {h})')
        for i, f in enumerate(self.fields):
            ch.append(f"Eq ({f[0]}.At {off('s.regs.rbx.toBitVec', self.sszoff(i))})")
        rc = 's.regs.rax.toBitVec'
        if self.st: ch.append(f'Eq (ast.At {rc})')
        bi = 0
        hp = []
        for i, f in enumerate(self.fields):
            g = self.gooff(i)
            if f[1] == 'bytes':
                if i < done:
                    bi += 1
                    ch += [f'Eq ((Int.toBytes 8 p{bi}.toInt).At {off(rc, g)})',
                           f'Eq ((Int.toBytes 8 {f[2]}).At {off(rc, g + 8)})',
                           f'Eq ((Int.toBytes 8 {f[2]}).At {off(rc, g + 16)})']
                    hp.append(f'Eq ({f[0]}.At p{bi})')
                else:
                    ch += [f'Eq (aP{i}.At {off(rc, g)})', f'Eq (aL{i}.At {off(rc, g + 8)})',
                           f'Eq (aC{i}.At {off(rc, g + 16)})']
            else:
                ch.append(f"Eq ({f[0] if i < done else f'aN{i}'}.At {off(rc, g)})")
        ch += hp
        if self.rt: ch.append('Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)')
        ch.append('R')
        return ('\n' + ind + '⋆ ').join(ch)

    # ---- binders
    def binders(self):
        C = self.C
        s = f"∀ (k : Nat) (hk : {C}.IsInfixAt Host.prog k) (hf : LabelsFresh {C} k)\n"
        for prog, suf, _ in self.callees:
            s += f"    (k{suf} : Nat) (hk{suf} : {prog}.IsInfixAt Host.prog k{suf}) (hf{suf} : LabelsFresh {prog} k{suf})\n"
        vn = [f[0] for f in self.fields]
        s += f"    ({' '.join(vn)} : List UInt8) " + ' '.join(f'(h{f[0]} : {f[0]}.length = {self.fsize(f)})' for f in self.fields) + '\n'
        s += "    (s : MachineData) (ra guard : UInt64)\n"
        s += f"    ({' '.join(self.cs)} : List UInt8)\n    "
        ln = {n: l for n, l, _ in self.stack}
        s += ' '.join(f'(h{c} : {c}.length = {ln.get(c, 8)})' for c in self.cs if ln.get(c, 8) is not None) + '\n'
        s += "    (R : DataMem → Prop)"
        if self.rt:
            s += " (S : Nat)" + (" (hS : S < 2 ^ 60)" if self.rt['hS'] else '') + f" (hlo : {self.lo_name}.length = {self.Sx})\n"
            s += "    (Heap : Nat → DataMem → Prop) (avail : Nat)"
        return s + '\n'

    def names(self):
        n = ['k', 'hk', 'hf']
        for _, suf, _ in self.callees: n += [f'k{suf}', f'hk{suf}', f'hf{suf}']
        n += [f[0] for f in self.fields] + ['h' + f[0] for f in self.fields] + ['s', 'ra', 'guard'] + self.cs
        ln = {x: l for x, l, _ in self.stack}
        n += ['h' + c for c in self.cs if ln.get(c, 8) is not None] + ['R']
        if self.rt: n += ['S'] + (['hS'] if self.rt['hS'] else []) + ['hlo', 'Heap', 'avail']
        return ' '.join(n)

    def hguard(self):
        return f"(hguard : guard.toNat{'' if self.gd == 0 else f' + {self.gd}'} < s.regs.rsp.toNat)"

    def rthyps(self):
        if not self.rt: return ''
        return (f" (hav : {self.heap(len(self.fields))} ≤ avail)\n    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 "
                f"{'S' if self.rt['x'] == 0 else '(' + self.Sx + ')'}) (hmm : MemmoveC {'S' if self.rt['x'] == 0 else '(' + self.Sx + ')'})")

    def rtnames(self): return ' hav hms hmm' if self.rt else ''

    def entry_prem(self):
        return (f"    (h_mem : s.dmem =⋆ {self.mem(self.pre, 0, [])})\n    {self.hguard()} "
                f"(hlen : s.regs.rcx = {self.ssz()}){self.rthyps()}")

    # ---- state predicates
    def xnames(self, d): return [f'x{i}' for i in range(len(d['exs']))]
    def pnames(self, d): return [f'p{i + 1}' for i in range(self.nb(d['done']))]

    def exbind(self, ps, xs, exs):
        s = ''
        if ps or xs:
            s = '∃' + (f" ({' '.join(ps)} : BitVec 64)" if ps else '') + (f" ({' '.join(xs)} : List UInt8)" if xs else '') + ', '
            s += ''.join(f"{x}.length = {self.Sx if e == 'lo' else e} ∧ " for x, e in zip(xs, exs))
        return s

    def stp(self, d, st='st'):
        p = [f"{st}.pc = Host.addrOf (k + {d['pc']})",
             f"{st}.data.regs.rsp = {{ toBitVec := s.regs.rsp.toBitVec - {self.frame} }}",
             f"{st}.data.regs.rbp = {{ toBitVec := s.regs.rsp.toBitVec - 8 }}", f"{st}.data.regs.r14 = s.regs.r14"]
        p += [f"{st}.data.regs.get64 Reg64.{r} = {RVT[v]}" for r, v in d['regs']]
        xs = self.xnames(d)
        return ('\n        ∧ '.join(p) + ' ∧\n        ' + self.exbind(self.pnames(d), xs, d['exs'])
                + f"\n        ({self.mem(d['stk'], d['done'], xs, '          ')}) {st}.data.dmem")

    def final(self, st='st'):
        n = len(self.fields)
        xs = [f'x{i}' for i in range(len(self.exs))]
        ps = [f'p{i + 1}' for i in range(self.nb(n))]
        return (f"{st}.pc = Int64.ofBitVec ra.toBitVec ∧ {st}.data.regs.rax = 0 ∧ {st}.data.regs.rbx = 0\n"
                f"        ∧ {st}.data.regs.rsp = s.regs.rsp + 8 ∧ {st}.data.regs.rbp = s.regs.rbp ∧ {st}.data.regs.r14 = s.regs.r14 ∧\n"
                f"        {self.exbind(ps, xs, self.exs)}\n        ({self.mem(self.post, n, xs, '          ')}) {st}.data.dmem")

    def rin(self, d):
        regs = [f'hr{r}' for r, _ in d['regs']]
        xs = self.xnames(d)
        return (['hpc', 'hrsp', 'hrbp', 'hr14'] + regs + self.pnames(d) + xs + ['h' + x for x in xs] + ['Hm'], regs)

    def opts(self, big):
        return f"set_option maxHeartbeats {16000000 if big else 4000000} in\nset_option maxRecDepth 100000 in\n"

    def kind(self, name, kind, extra):
        self.kinds_emitted.append((name, kind))
        return (f"theorem {name}_kind : ∀ (h : Host), type_of% (@{name} h)\n    = @Codec.{kind} h {self.Cq} {self.L} {self.fieldslean()}"
                f"{extra} := by\n  intro h; rfl\n\n")

    # ---- common proof prefix of field / epilogue theorems
    def prefix(self, d, hyps, destructure=True):
        pat, regs = self.rin(d)
        s = f"  intro {self.names()}{hyps}\n" + destr('s')
        s += "  simp only at hguard ⊢\n" if 'hguard' in hyps else "  simp only at ⊢\n"
        s += f"  rintro ⟨d, pc⟩ ⟨{', '.join(pat)}⟩\n"
        s += f"  dsimp only at hpc hrsp hrbp hr14 {' '.join(regs)} Hm\n  subst hpc\n"
        if destructure:
            s += destr('d', '1')
            s += f"  simp only [Reg64s.get64] at hrsp hrbp hr14 {' '.join(regs)} Hm\n  subst rsp1 rbp1 r141\n"
            for (r, v), h in zip(d['regs'], regs):
                tgt = {'rcv': 'rax', 'bf': 'rbx', 'zero': '(0 : UInt64)'}[v]
                if v == 'zero':
                    s += f"  obtain rfl : {tgt} = {r}1 := (UInt64.toBitVec_inj.mp (show {r}1.toBitVec = (0 : UInt64).toBitVec from {h})).symm\n"
                else:
                    s += f"  obtain rfl : {tgt} = {r}1 := (UInt64.toBitVec_inj.mp {h}).symm\n"
        return s

    def slot_at(self, d, o):
        for sl in d['stk']:
            if sl[0] == 'at' and sl[1] == o: return sl[2]
        refuse(f'gen5: no stack slot at entry offset {o}')

    def lo_val(self, d):
        for sl in d['stk']:
            if sl[0] == 'lo': return sl[1]
        refuse('gen5: no low-stack slot')

    # ---- head
    def head(self):
        h = self.headspec
        d0 = self.states[0]
        name = f'{self.ns}_head'
        s = self.opts(False) + f"/-- Head: directives 0–{d0['pc'] - 1} (prologue, spills{', nil check' if h.get('nil') is not None else ''}); entry → boundary state 0. -/\n"
        s += f"theorem {name} : {self.binders()}{self.entry_prem()},\n    Eventually (step1 Host.exe)\n      (fun st => {self.stp(d0)})\n      ⟨s, Host.addrOf k⟩ := by\n"
        s += f"  intro {self.names()} h_mem hguard hlen{self.rtnames()}\n"
        if h.get('nil') is not None:
            s += ("  have hcs : Eq (ast.At s.regs.rax.toBitVec) =\n      Eq ((ast.take 1).At s.regs.rax.toBitVec) ⋆ Eq ((ast.drop 1).At (s.regs.rax.toBitVec + 1)) := by\n"
                  "    conv => lhs; rw [← List.take_append_drop 1 ast]\n"
                  "    exact at_app _ _ (by rw [List.length_take, hast]; rfl) (by simp [hast])\n  rw [hcs] at h_mem\n")
        hg = 'hguard' if self.gd == 0 else f'(Nat.lt_of_le_of_lt (Nat.le_add_right _ {self.gd}) hguard)'
        fpn = self.slot_at({'stk': self.pre}, -8)[1]
        s2n = self.slot_at({'stk': self.pre}, 16)[1]
        s += (f"  refine eventually_trans _ _ _ _ (decpro_seg _ _ _ _ {h['F']} {h['dB']} {self.ssz()} _ k (k + 11) (win hk 0 11) (by rfl) (by rfl)\n"
              f"    s ra guard (s.regs.rsp.toBitVec - {self.frame}) (s.regs.rsp.toBitVec + 16)\n    {ADDR} {ADDR}\n"
              f"    {fpn} {s2n} h{fpn} h{s2n} _ (by ecancel) {hg} (by rw [hlen]; rfl)) ?_\n"
              "  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hreg1, Hm1⟩\n  dsimp only at hpc1 hrsp1 hrbp1 hreg1 Hm1\n  subst hpc1\n")
        for r in ['rax', 'rbx', 'rdi', 'r14']:
            s += f"  have h{r}1 := UInt64.toBitVec_inj.mp (hreg1 Reg64.{r} (by decide) (by decide))\n"
        s += "  clear hreg1\n" + destr('d1', '1')
        s += "  simp only at hrsp1 hrbp1 hrax1 hrbx1 hrdi1 hr141 Hm1\n  subst hrsp1 hrbp1 hrax1 hrbx1 hrdi1 hr141\n"
        i = 11
        for r, disp in h['spills']:
            o = disp - self.frame
            old, hold = ('(Int.toBytes 8 s.regs.rbx.toBitVec.toInt)', LEN) if r == 'rbx' else self.vterm(self.slot_at({'stk': self.pre}, o), [])
            s += (f"  apply kstep_st Reg64.{r} Reg64.rsp {disp} _ (k + {i}) (k + {i + 1}) (win hk {i} 1) (by rfl) (by rfl)\n"
                  f"    (s.regs.rsp.toBitVec - {self.frame}) {soff(o)} {ADDR}\n    {old} {hold} _ _ _ (by rfl) (by ecancel)\n"
                  f"  intro m{i} H{i}; kn; simp only [Reg64s.get64] at H{i}\n")
            i += 1
        if h.get('nil') is not None:
            s += (f"  apply kstep_nilchk Reg64.rax _ (k + {i}) (k + {i + 1}) (win hk {i} 1) (by rfl) (by rfl)\n"
                  "    s.regs.rax.toBitVec (ast.take 1) (by simp [hast]) _ _ _ (by rfl) (by ecancel)\n  intro fl; kn\n")
            i += 1
        if i != d0['pc']:
            refuse(f'gen5 head: rendered up to directive {i}, boundary state 0 at {d0["pc"]}')
        s += "  apply Eventually.done\n  refine ⟨rfl, rfl, rfl, rfl, " + ''.join('rfl, ' for _ in d0['regs']) + "?_⟩\n  dsimp only\n"
        if h.get('nil') is not None: s += "  rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]\n"
        s += "  ecancel\n"
        return s + self.kind(name, 'decHeadKindN', f"\n    {self.dlean(d0)}")

    # ---- field theorems
    def field(self, i):
        d, d2, f = self.states[i], self.states[i + 1], self.fspec[i]
        name = f'{self.ns}_f{i + 1}'
        big = f['shape'] == 'bytes'
        s = self.opts(big) + f"/-- Field {i + 1} `{f['name']}` ({f['shape']}): boundary state {i} (directive {d['pc']}) → boundary state {i + 1} (directive {d2['pc']}). -/\n"
        s += (f"theorem {name} : {self.binders()}    {self.hguard()}{self.rthyps()} (st0 : MachineState),\n"
              f"    ({self.stp(d, 'st0')}) →\n    Eventually (step1 Host.exe)\n      (fun st => {self.stp(d2)})\n      st0 := by\n")
        hy = ' hguard' + self.rtnames()
        s += {'u64': self.f_u64, 'bytes': self.f_bytes, 'call': self.f_call}[f['shape']](i, d, d2, f, hy)
        return s + self.kind(name, 'decFieldKindN', f"\n    {self.dlean(d)}\n    {self.dlean(d2)}")

    def f_u64(self, i, d, d2, f, hy):
        s = self.prefix(d, hy)
        s += ''.join(P(l) + '\n' for l in f['steps'])
        xs = self.xnames(d)
        s += "  apply Eventually.done\n  refine ⟨rfl, rfl, rfl, rfl, " + ''.join('rfl, ' for _ in d2['regs'])
        s += ''.join(x + ', ' for x in self.pnames(d) + xs + ['h' + x for x in xs]) + "?_⟩\n  dsimp only\n  ecancel\n"
        return s

    def f_bytes(self, i, d, d2, f, hy):
        fr = self.frame
        pre = f.get('pre', [])
        s = self.prefix(d, hy, destructure=bool(pre))
        s += ''.join(P(l) + '\n' for l in pre)
        xs = self.xnames(d)
        n = self.fields[i][2]
        v = self.fields[i][0]
        g = self.gooff(i)
        so = self.sszoff(i)
        z = so == 0
        aret = -(fr + 8)
        one = not any(sl[0] == 'at' and sl[1] == -fr + 8 for sl in d['stk'])
        if one: spl, hspl = self.vterm(self.slot_at(d, -fr), xs)
        memp = '(by ecancel)'
        if not one:
            tr = [self.vterm(self.slot_at(d, -fr + 8 * j), xs) for j in range(3)]
            spl = f'({tr[0][0]} ++ ({tr[1][0]} ++ {tr[2][0]}))'
            hspl = '(by simp only [List.length_append, Int.toBytes_length, ' + ', '.join(h for _, h in tr if h != LEN) + '])'
            memp = (f"(by rw [frame_j3 {soff(-fr)} {soff(-fr + 8)} {soff(-fr + 16)} _ _ _ {tr[0][1]} {tr[1][1]} {tr[2][1]} (by bv_omega) (by bv_omega)]; ecancel)")
        rs, hrs = self.vterm(self.slot_at(d, aret), xs)
        lo, hlo = self.vterm(self.lo_val(d), xs)
        ls, hls = self.vterm(self.slot_at(d, f['dS'] - fr), xs)
        x = self.rt['x']
        hLo = f"(frame_lo _ {fr} {self.rt['loB']} S (by decide))" if x == 8 else f"(frame_lo0 _ {fr} {self.rt['loB']} S (by decide))"
        St = '(S + 8)' if x == 8 else 'S'
        h0 = self.heap(i)
        av = 'avail' if h0 == 0 else f'(avail - {h0})'
        rc, bf = 's.regs.rax.toBitVec', 's.regs.rbx.toBitVec'
        state = "_ (by rfl) (by rfl) (by rfl)" if pre else "d hrsp hrbp hr14"
        call = (f"  refine eventually_trans _ _ _ _ ({f['seg']} k hk hf (s.regs.rsp.toBitVec - {fr}) {rc} {bf}\n"
                f"    {soff(f['dR'] - fr)} {soff(f['dB'] - fr)} {soff(f['dS'] - fr)} {soff(aret)}\n"
                f"    {self.lo_addr()} {off(rc, g)} {off(rc, g + 8)} {off(rc, g + 16)}{'' if z else ' ' + off(bf, so)} {St}\n"
                f"    {ADDR} {ADDR} {ADDR} (by bv_omega) {hLo}\n"
                f"    {ADDR0 if g == 0 else ADDR} {ADDR} {ADDR}{'' if z else ' ' + ADDR}\n"
                f"    {{ toBitVec := s.regs.rsp.toBitVec - 8#64 }} s.regs.r14 {v} h{v}\n"
                f"    {spl} {rs} {lo} {ls} aP{i} aL{i} aC{i}\n"
                f"    {hspl} {hrs} {hlo} {hls} haP{i} haL{i} haC{i}\n"
                f"    _ Heap {av} (by omega) {state}\n      {memp} hms hmm) ?_\n")
        s += P(call)
        pn = f'p{self.nb(i) + 1}'
        t = f['tail']
        s += (f"  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hr14', {pn}, spl', lo', hspl', hlo', hrY, Hm'⟩\n"
              "  dsimp only at hpc' hrsp' hrbp' hr14' hrY Hm'\n  subst hpc'\n" + destr("d'", '2') +
              "  simp only at hrsp' hrbp' hr14' hrY Hm'\n  subst rsp2 rbp2 r142\n")
        s += P(f"  apply {self.ns}_s{t[0]} k hk hf (s.regs.rsp.toBitVec - {fr}) {soff(f['dS'] - fr)} {pn} {ADDR} _ _ _ (by rfl) (by ecancel)\n  kn\n"
               f"  apply {self.ns}_s{t[1]} k hk hf\n  apply {self.ns}_s{t[2]} k hk hf\n"
               f"  apply {self.ns}_s{t[3]} k hk hf {rc} {off(rc, g)} {ADDR0 if g == 0 else ADDR} (Int.toBytes 8 {pn}.toInt) {LEN} _ _ _\n"
               "    (by exact hrY) (by ecancel)\n  intro m' H\n  kn\n  simp only [Reg64s.get64] at H\n")
        if d2['exs'] != [24, 'lo']:
            refuse(f'gen5 field {i + 1}: post state existentials {d2["exs"]} (byte recipe: [24, lo])')
        regp = ''.join('hrY, ' for _ in d2['regs'])
        s += ("  apply Eventually.done\n  refine ⟨rfl, rfl, rfl, rfl, " + regp + ''.join(p + ', ' for p in self.pnames(d2))
              + "spl', lo', hspl', hlo', ?_⟩\n  dsimp only\n")
        s += f"  rw [show k + {f['jm']} + 1 = k + {f['jm'] + 1} from rfl] at H\n"
        if h0: s += f"  rw [show avail - {h0} - {n} = avail - {h0 + n} by omega] at H\n"
        return s + "  ecancel\n"

    def f_call(self, i, d, d2, f, hy):
        fr = self.frame
        s = self.prefix(d, hy)
        prog, suf, thm = [c for c in self.callees if c[1] == f['callee']][0]
        s += f"  have hC := {thm} k{suf} hk{suf} hf{suf}\n"
        s += (f"  have hg : guard.toNat < (rsp.toBitVec - {self.gd}).toNat := by\n"
              f"    have hgd : guard.toNat + {self.gd} < rsp.toBitVec.toNat := hguard\n    bv_omega\n")
        xs = self.xnames(d)
        aret, afp, as2 = -(fr + 8), -(fr + 16), -(fr - 8)
        if self.gd != fr + 8:
            refuse('gen5: call field with a guard addend other than frame + 8')
        so, g = self.sszoff(i), self.gooff(i)
        v = self.fields[i][0]
        src = off('rbx.toBitVec', so)
        dst = off('rax.toBitVec', g)
        rs, hrs = self.vterm(self.slot_at(d, aret), xs)
        mix = bool(self.rt)
        post_x = []
        goalrw = []
        if mix:
            merged = not any(sl[0] == 'at' and sl[1] == as2 for sl in d['stk'])
            lo, hlo = self.vterm(self.lo_val(d), xs)
            if merged:
                X, hX = self.vterm(self.slot_at(d, -fr), xs)
                s += (f"  have hq0 : ({X}.take 8).length = 8 := by simp [{hX}]\n"
                      f"  have hq1 : (({X}.drop 8).take 8).length = 8 := by simp [{hX}]\n"
                      f"  have hq2 : (({X}.drop 8).drop 8).length = 8 := by simp [{hX}]\n"
                      f"  have hXs : {X} = {X}.take 8 ++ (({X}.drop 8).take 8 ++ ({X}.drop 8).drop 8) := by\n"
                      "    rw [List.take_append_drop, List.take_append_drop]\n")
                s2, hs2 = f'(({X}.drop 8).take 8)', 'hq1'
            else:
                s2, hs2 = self.vterm(self.slot_at(d, as2), xs)
            s += (f"  have hlS : ({lo}.take S).length = S := by simp [{hlo}]\n"
                  f"  have hl8 : ({lo}.drop S).length = 8 := by simp [{hlo}]\n"
                  f"  have hLs : {lo} = {lo}.take S ++ {lo}.drop S := (List.take_append_drop S {lo}).symm\n")
            j3 = P(f"frame_j3 {soff(-fr)} {soff(-fr + 8)} {soff(-fr + 16)} _ _ _")
            lo8 = P(f"frame_lo8 (s.regs.rsp.toBitVec - {self.rt['loB']}) S hS _ _")
            if merged:
                s += f"  rw [hXs, hLs, {j3} hq0 hq1 hq2 (by bv_omega) (by bv_omega), {lo8} hlS hl8] at Hm\n"
                post_x.append((f"({X}.take 8 ++ (Int.toBytes 8 {src}.toInt ++ ({X}.drop 8).drop 8))",
                               "(by simp only [List.length_append, hq0, hq2, Int.toBytes_length])"))
                goalrw = [f"{j3} hq0 {LEN} hq2 (by bv_omega) (by bv_omega)"]
            else:
                s += f"  rw [hLs, {lo8} hlS hl8] at Hm\n"
                post_x.append((f"(Int.toBytes 8 {src}.toInt)", LEN))
            fp, hfp = f'({lo}.drop S)', 'hl8'
            post_x.append((f"({lo}.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt)",
                           "(by simp only [List.length_append, hlS, Int.toBytes_length])"))
            goalrw.append(f"{lo8} hlS {LEN}")
        else:
            s2, hs2 = self.vterm(self.slot_at(d, as2), xs)
            fp, hfp = self.vterm(self.slot_at(d, afp), xs)
            post_x = [(f"(Int.toBytes 8 {src}.toInt)", LEN), ("(Int.toBytes 8 (rsp.toBitVec - 8#64).toInt)", LEN)]
        s += ''.join(P(l) + '\n' for l in f['steps'])
        s += P(f"  refine eventually_trans _ _ _ _ ({f['call']} k hk hf hC (s.regs.rsp.toBitVec - {fr}) {dst} {src}\n"
               f"    {soff(aret)} {soff(afp)} {soff(as2)} (by bv_omega) (by bv_omega) (by bv_omega)\n"
               f"    {{ toBitVec := s.regs.rsp.toBitVec - 8#64 }} s.regs.r14 guard {v} {rs} {fp} {s2} aN{i}\n"
               f"    h{v} {hrs} {hfp} {hs2} haN{i} hg _ _\n"
               "    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide) (by ecancel)) ?_\n")
        s += ("  rintro ⟨d', pc'⟩ ⟨hpc', hrax', hrbx', hrsp', hrbp', hr14', Hm'⟩\n"
              "  dsimp only at hpc' hrax' hrbx' hrsp' hrbp' hr14' Hm'\n  apply Eventually.done\n")
        rp = {'rax': "(congrArg UInt64.toBitVec hrax')", 'rbx': "(congrArg UInt64.toBitVec hrbx')"}
        if not all(r in rp and vv == 'zero' for r, vv in d2['regs']):
            refuse(f'gen5 field {i + 1}: register facts after a call field {d2["regs"]} (recipe: rax / rbx zero)')
        regp = ''.join(rp[r] + ', ' for r, vv in d2['regs'])
        if len(post_x) != len(d2['exs']):
            refuse(f'gen5 field {i + 1}: {len(post_x)} chunk witnesses, {len(d2["exs"])} existentials')
        s += ("  refine ⟨hpc', hrsp', hrbp', hr14', " + regp + ''.join(p + ', ' for p in self.pnames(d2))
              + ', '.join(w for w, _ in post_x) + ',\n    ' + ', '.join(h for _, h in post_x) + ", ?_⟩\n  dsimp only\n")
        if goalrw: s += f"  rw [{', '.join(goalrw)}]\n"
        s += f"  rw [show k + {f['jc']} + 1 = k + {f['jc'] + 1} from rfl] at Hm'\n  ecancel\n"
        return s

    # ---- epilogue
    def epi(self):
        d = self.states[-1]
        e = self.epispec
        name = f'{self.ns}_epi'
        fr = self.frame
        s = self.opts(False) + f"/-- Epilogue: boundary state {len(self.states) - 1} (directive {d['pc']}) → return. -/\n"
        s += (f"theorem {name} : {self.binders()}    (st0 : MachineState),\n    ({self.stp(d, 'st0')}) →\n"
              f"    Eventually (step1 Host.exe)\n      (fun st => {self.final()})\n      st0 := by\n")
        xs = self.xnames(d)
        tail = ("  rintro ⟨d', pc'⟩ ⟨hpc', hrax', hrbx', hrsp', hrbp', hr14', hmem'⟩\n"
                "  dsimp only at hpc' hrax' hrbx' hrsp' hrbp' hr14' hmem'\n  apply Eventually.done\n"
                "  refine ⟨hpc', hrax', hrbx', ?_, hrbp', hr14', " + ''.join(x + ', ' for x in self.pnames(d) + xs + ['h' + x for x in xs]) + "?_⟩\n"
                "  · rw [hrsp']; apply UInt64.toBitVec_inj.mp\n"
                "    first\n      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; done)\n"
                "      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)\n")
        a = e['add']
        if e['form'] == 'e20':
            s += self.prefix(d, '', destructure=False)
            s += (f"  have hE := Codec.infix_sub (q := Codec.decEpi) {a} hk\n"
                  f"    (by simp only [{self.Cq}, Codec.decEpi, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])\n")
            s += P(f"  refine eventually_trans _ _ _ _ (Codec.decepi_seg (k + {a}) hE (s.regs.rsp.toBitVec - {fr}) (s.regs.rsp.toBitVec - 8) s.regs.rsp.toBitVec\n"
                   "    (by bv_omega) (by bv_omega) rbp ra r14 _ d hrsp hr14 (by ecancel)) ?_\n")
            s += tail + "  · dsimp only; ecancel\n"
        else:
            s += self.prefix(d, '')
            s += ''.join(P(l) + '\n' for l in e.get('pre', []))
            s += P(f"  refine eventually_trans _ _ _ _ (decepi_n {e['F']} _ (k + {a}) (k + {a + 1}) (win hk {a} 1) (by rfl) (by rfl)\n"
                   f"    _ (win hk {a + 1} 2) (by rfl) (s.regs.rsp.toBitVec - {fr}) (s.regs.rsp.toBitVec - 8) s.regs.rsp.toBitVec\n"
                   f"    {ADDR} (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_\n")
            s += tail + "  · dsimp only; rw [hmem']; ecancel\n"
        return s + self.kind(name, 'decEpiKindN', f"\n    {self.dlean(d)}")

    # ---- accept
    def accept(self):
        name = f'{self.ns}_accept'
        a = self.names()
        s = self.opts(True) + (f"/-- **Accept path of `{self.go}`, generated proof** (`p2dec --gen5`): head, one theorem per\n"
                               "field, epilogue, chained by `eventually_trans`. Statement = the kind instance (`_kind`). -/\n")
        s += (f"theorem {name} : {self.binders()}{self.entry_prem()},\n    Eventually (step1 Host.exe)\n"
              f"      (fun st => {self.final()})\n      ⟨s, Host.addrOf k⟩ := by\n")
        s += f"  intro {a} h_mem hguard hlen{self.rtnames()}\n"
        s += f"  refine eventually_trans _ _ _ _ ({self.ns}_head {a} h_mem hguard hlen{self.rtnames()}) ?_\n  intro st0 h0\n"
        n = len(self.fields)
        for i in range(n):
            s += f"  refine eventually_trans _ _ _ _ ({self.ns}_f{i + 1} {a} hguard{self.rtnames()} st{i} h{i}) ?_\n  intro st{i + 1} h{i + 1}\n"
        s += f"  exact {self.ns}_epi {a} st{n} h{n}\n"
        s += self.kind(name, 'decAcceptKindN', '')
        if self.same_as_prop:
            s += (f"/-- Statement check: the generated theorem proves the independently written hand statement `{self.same_as_prop}`. -/\n"
                  f"theorem {name}_stmt : {self.same_as_prop} := {name}\n\n")
        if self.same_as:
            s += (f"/-- Statement check: the declared type is the type of the independently written hand theorem `{self.same_as}`. -/\n"
                  f"theorem {name}_same : ∀ (h : Host), type_of% (@{name} h) = type_of% (@{self.same_as} h) := by\n  intro h; rfl\n\n")
        return s

    # ---- size reject
    def reject(self):
        r = self.rejspec
        name = f'{self.ns}_reject'
        C = self.Cq
        s = ("set_option maxRecDepth 100000 in\n"
             f"/-- Size reject (`rcx ≠ {self.ssz()}`): `decrej_seg` (frame `{r['F']:#x}`, error block at {r['jl']}). -/\n"
             f"theorem {name} : ∀ (k : Nat) (hk : {C}.IsInfixAt Host.prog k) (hf : LabelsFresh {C} k)\n"
             "    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)\n"
             "    (R : DataMem → Prop)\n"
             "    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)\n"
             "      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))\n"
             "      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))\n"
             "      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)\n"
             "      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label \"ssz.ErrSize\" + 8).toBitVec) ⋆ R)\n"
             f"    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ {self.ssz()}),\n"
             "    Eventually (step1 Host.exe)\n"
             "      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1\n"
             "        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14\n"
             "        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)\n"
             "          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))\n"
             "          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))\n"
             "          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))\n"
             "          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)\n"
             "          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label \"ssz.ErrSize\" + 8).toBitVec) ⋆ R) st.data.dmem)\n"
             "      ⟨s, Host.addrOf k⟩ := by\n"
             "  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen\n"
             f"  have hl := Machine.label_at' hk hf (j := {r['jl']})\n"
             f"    (by simp only [{C}, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)\n"
             f"    (by simp only [{C}, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)\n"
             f"  exact decrej_seg _ _ _ _ {r['F']} {r['dB']} {self.ssz()} _ k (win hk 0 11) (by rfl) (by decide)\n"
             f"    _ (k + {r['jl']}) (k + {r['jl'] + 3}) (win hk {r['jl']} 3) (by rfl) (by rfl) hl\n"
             f"    _ (k + {r['jl'] + 4}) (win hk {r['jl'] + 3} 1) (by rfl) (by rfl) _ (win hk {r['jl'] + 4} {r['nret']}) (by rfl)\n"
             "    s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard (fun h => hlen (h.trans (by rfl)))\n")
        self.kinds_emitted.append((name, 'decRejectKindN'))
        s += (f"theorem {name}_kind : ∀ (h : Host), type_of% (@{name} h)\n    = @Codec.decRejectKindN h {C} {self.ssz()} := by\n"
              "  intro h; with_reducible rfl\n\n")
        return s

    def body(self):
        """All GEN5 theorems, in dependency order (head, fields, epilogue, accept, reject)."""
        self.kinds_emitted = []
        s = self.head()
        for i in range(len(self.fields)):
            s += self.field(i)
        s += self.epi() + self.accept()
        if self.rejspec is not None:
            s += self.reject()
        return s


# --------------------------------------------------------------------------------------------- derivation

def _hx(s):
    return int(s, 16)


def g5_head_spec(dirs, head_end, F, st):
    """The decPro prologue (fixed positions, the `nop` at 8), dB = F + 24, then the spills of rax / rbx / rdi to their
    home slots (entry rsp + 8 / 16 / 32) and the optional nil check. Anything else: refuse."""
    want = [None, None, r"cmp 0x10\(%r14\),%rsp", r"jbe \S+", r"push %rbp", r"mov %rsp,%rbp", r"sub \$(0x[0-9a-f]+),%rsp",
            r"mov %rbx,(0x[0-9a-f]+)\(%rsp\)", r"nop", r"cmp \$(0x[0-9a-f]+),%rcx", r"jne (\S+)"]
    ms = []
    for i, rx in enumerate(want):
        if rx is None:
            continue
        m = re.fullmatch(rx, dirs[i])
        if not m:
            refuse(f"gen5 head: directive {i} `{dirs[i]}` is not /{rx}/ (decpro_seg window, nop at 8)")
        ms.append(m)
    if _hx(ms[4].group(1)) != F:
        refuse("gen5 head: frame size differs from the GEN4 head")
    dB = _hx(ms[5].group(1))
    if dB != F + 24:
        refuse(f"gen5 head: rbx spill at {dB:#x}, decpro_seg needs F + 24 = {F + 24:#x}")
    frame = F + 8
    home = {'rax': 8, 'rbx': 16, 'rdi': 32}
    spills = []
    i = 11
    while i < head_end:
        m = re.fullmatch(r"mov %(rax|rbx|rdi),(0x[0-9a-f]+)\(%rsp\)", dirs[i])
        if not m:
            break
        r, d = m.group(1), _hx(m.group(2))
        if d - frame != home[r]:
            refuse(f"gen5 head: directive {i} `{dirs[i]}` spills {r} to entry rsp + {d - frame} (home slot {home[r]})")
        spills.append((r, d))
        i += 1
    nil = None
    if i < head_end and dirs[i] == "test %al,(%rax)":
        if not st:
            refuse("gen5 head: nil check without a state word (not exercised)")
        nil = i
        i += 1
    if i != head_end:
        refuse(f"gen5 head: directive {i} `{dirs[i]}` between the spills and the end of the GEN4 head ({head_end})")
    if len({r for r, _ in spills}) != len(spills):
        refuse("gen5 head: a register is spilled twice")
    return dict(F=F, dB=dB, spills=spills, nil=nil, jne=ms[8].group(1))


def g5_reject_spec(dirs, head, label_index):
    """The `jne` target of directive 10 must be the error block `lerr: mov ssz.ErrSize(%rip),%rax;
    mov ssz.ErrSize+8(%rip),%rbx; add $F,%rsp; pop %rbp; retq` (no nop inside)."""
    F = head['F']
    jl = label_index(dirs, head['jne'])
    blk = dirs[jl:jl + 5]
    want = [f"{head['jne']}:", "mov ssz.ErrSize(%rip),%rax", "mov ssz.ErrSize+8(%rip),%rbx", f"add ${F:#x},%rsp",
            "pop %rbp"]
    if blk != want:
        refuse(f"gen5 reject: the size-error block at {jl} is not {want} + `retq` (it is {dirs[jl:jl + 6]})")
    # `pop %rbp`, then `nop`s (the `decRet` window erases them, `eraseNop`), then `retq`
    m = 1
    while jl + 4 + m < len(dirs) and dirs[jl + 4 + m] == "nop" and m < 4:
        m += 1
    if jl + 4 + m >= len(dirs) or dirs[jl + 4 + m] != "retq":
        refuse(f"gen5 reject: no `retq` after `pop %rbp` (only nops between) in the size-error block at {jl}")
    return dict(F=F, dB=head['dB'], jl=jl, nret=m + 1)


def g5_derive(dirs, fields, head_end, F, done, end, args, label_index):
    """Build the description `T` of the accept proof from the GEN4 walk. `fields` are the IR fields
    (name, SSZ offset, Go offset, class, info); `done` the GEN4 units per field (complete, IR order); `end` the
    directive after the last field event. Raises G5Refuse on everything outside the recipes."""
    n = len(fields)
    if [x for x, _ in done] != list(range(n)) or n == 0:
        refuse("gen5: the GEN4 walk did not complete every IR field in order")
    # ---- fields: kinds, sizes, offsets (Go offsets = the running sum of the kind)
    st = fields[0][2] == 8
    if fields[0][2] not in (0, 8):
        refuse(f"gen5: first Go offset {fields[0][2]} (kind: 0, or 8 with a state word)")
    fl = []
    so = 0
    go = 8 if st else 0
    for i, (fname, src, fo, cls, info) in enumerate(fields):
        if cls == 'bytes':
            if info not in (32, 48, 96):
                refuse(f"gen5: field {fname}: byte size {info}")
            fl.append((f'fv{i}', 'bytes', info))
            sz, gz = info, 24
        elif cls in ('u64', 'call'):
            if cls == 'call' and info not in G5_CALLEES:
                refuse(f"gen5: field {fname}: callee {info} has no proved spec")
            fl.append((f'fv{i}', 'u64'))
            sz, gz = 8, 8
        else:
            refuse(f"gen5: field {fname}: class {cls} (no recipe)")
        if src != so or fo != go:
            refuse(f"gen5: field {fname}: IR SSZ offset {src} / Go offset {fo}, the kind's running sums {so} / {go}")
        so += sz
        go += gz
    frame = F + 8
    head = g5_head_spec(dirs, head_end, F, st)
    units = [us for _, us in done]
    has_rt = any(u['kind'] == 'seg' for us in units for u in us)
    has_call = any(u['kind'] == 'callblk' for us in units for u in us)
    if not has_rt and not has_call:
        refuse("gen5: no runtime call and no callee call (no recipe)")
    if not has_rt and any(f[1] == 'bytes' for f in fl):
        refuse("gen5: byte field without a segment")
    # callees in order of first callq
    callees = []
    for us in units:
        for u in us:
            if u['kind'] == 'callblk':
                c = G5_CALLEES.get(u['fn'])
                if c is None:
                    refuse(f"gen5: callee {u['fn']} without a proved spec")
                if c not in callees:
                    callees.append(c)
    # ---- written frame slots (sp displacement in [0x18, F)): stack stores of the steps and the segment pointer slots
    area = [0] if (has_rt and not has_call) else ([0, 8, 16] if has_rt else [8])
    written = set()
    for us in units:
        for u in us:
            if u['kind'] == 'st' and u['rB'] == 'rsp':
                d = u['disp']
                if not (0x18 <= d < F) or d % 8:
                    refuse(f"gen5: directive {u['jd']} `{u['text']}`: stack store at {d:#x} outside the frame slots [0x18, {F:#x})")
                written.add(d)
            if u['kind'] == 'seg':
                if not (0x18 <= u['dS'] < F):
                    refuse(f"gen5: pointer slot {u['dS']:#x} outside the frame slots")
                if u['dR'] != frame + 8 or u['dB'] != frame + 16:
                    refuse(f"gen5: segment reloads from {u['dR']:#x} / {u['dB']:#x}, not the receiver / buffer home slots")
                written.add(u['dS'])
    # ---- the stack chunks (name, length | None for the rt low stack, entry offset)
    stack = [('fp', 8, -8)]
    spill_offs = sorted({d - frame for _, d in head['spills']} | {16})
    for o in spill_offs:
        stack.append((f's{o // 8}', 8, o))
    if has_rt and not has_call:
        stack.append(('spl', 24, -frame))
    else:
        for a in area:
            stack.append((f'sp{a // 8}', 8, -frame + a))
    for d in sorted(written):
        stack.append((f'l{d:x}', 8, -frame + d))
    stack.append(('rslot', 8, -(frame + 8)))
    stack.append(('lo', None, None) if has_rt else ('lo', 8, -(frame + 16)))
    if len({o for _, _, o in stack if o is not None}) != len([1 for _, _, o in stack if o is not None]):
        refuse("gen5: two stack chunks at one offset")
    pre = [('lo', ('orig', 'lo')) if l is None else at(o, ('orig', nm)) for nm, l, o in stack]
    rt = dict(hS=has_call, x=8 if has_call else 0, loB=frame + 8 + (8 if has_call else 0)) if has_rt else None
    gd = frame + 8 if has_call else 0

    # ---- symbolic simulation: registers (only facts carried at boundaries) and the stack slots
    def setslot(stk, o, v):
        for sl in stk:
            if sl[0] == 'at' and sl[1] == o:
                sl[2] = v
                return
        refuse(f"gen5: no stack chunk at entry offset {o}")

    def getslot(stk, o):
        for sl in stk:
            if sl[0] == 'at' and sl[1] == o:
                return sl[2]
        refuse(f"gen5: no stack chunk at entry offset {o} (load / store outside the layout)")

    def setlo(stk, v):
        for sl in stk:
            if sl[0] == 'lo':
                sl[1] = v
                return
        refuse("gen5: no low-stack chunk")

    def mk(stk):
        return [list(sl) for sl in stk]

    def freeze(stk):
        return [tuple(sl) for sl in stk]

    stk = mk(pre)
    setslot(stk, -8, ('reg', 'rbp'))
    for r, d in head['spills']:
        setslot(stk, d - frame, ('reg', r))
    setslot(stk, 16, ('reg', 'rbx'))
    exs = []
    regs = {r: ('UNK',) for r in REGS16}
    regs.update(rax=('RCV', 0), rbx=('BF', 0))   # what the head establishes (decpro_seg preserves rax / rbx)

    def reads(us):
        return _rw(us)[0]

    def writes(us):
        return _rw(us)[1]

    def _rw(us):
        """Registers a unit list reads before it writes them (in G4_R64 order), and the registers it writes."""
        rd, wr = [], set()

        def r_(r):
            if r not in wr and r not in rd and r != 'rsp':
                rd.append(r)
        for u in us:
            k = u['kind']
            if k == 'ld':
                r_(u['rB']); wr.add(u['rD'])
            elif k == 'st':
                r_(u['rS']); r_(u['rB'])
            elif k in ('lea',):
                r_(u['rB']); wr.add(u['rD'])
            elif k == 'movrr':
                r_(u['rS']); wr.add(u['rD'])
            elif k == 'add':
                r_(u['rD']); wr.add(u['rD'])
            elif k == 'movi':
                wr.add(u['rD'])
            elif k == 'callblk':
                for r in ('rax', 'rbx', 'rcx'):
                    r_(r)
                wr.update(REGS16)
            elif k == 'seg':
                wr.update(REGS16)
            elif k in ('jmp', 'label'):
                pass
            else:
                refuse(f"gen5: unit kind {k}")
        return [r for r in REGS16 if r in rd], wr

    def facts(need, where):
        out = []
        for r in need:
            v = regs.get(r, ('UNK',))
            rv = {('RCV', 0): 'rcv', ('BF', 0): 'bf', ('ZERO',): 'zero'}.get(v)
            if rv is None:
                refuse(f"gen5: {where} reads {r} = {v}, not the receiver / buffer / zero at the boundary (interleaved "
                       "or unexpressible boundary state)")
            out.append((r, rv))
        return out

    # epilogue form and its register needs
    epi = g5_epi_spec(dirs, end, F, has_rt, has_call)
    # facts needed at boundary i: what field i + 1 reads before writing, plus what is needed at boundary i + 1 and
    # field i + 1 does not write (a fact is carried through a field that does not touch the register)
    needs = [None] * n + [list(epi['reads'])]
    for i in range(n - 1, -1, -1):
        rd, wr = reads(units[i]), writes(units[i])
        needs[i] = [r for r in REGS16 if r in rd or (r in needs[i + 1] and r not in wr)]
    states = []
    fspec = []
    regs0 = regs
    states.append(dict(pc=head_end, done=0, regs=facts(needs[0], 'field 1'), stk=freeze(stk), exs=list(exs)))
    bi = 0
    pfx = args.prefix
    for i, us in enumerate(units):
        fname = fields[i][0]
        # registers at the boundary: only the facts of the state
        regs = {r: ('UNK',) for r in REGS16}
        for r, rv in states[-1]['regs']:
            regs[r] = {'rcv': ('RCV', 0), 'bf': ('BF', 0), 'zero': ('ZERO',)}[rv]
        steps = []
        blk = None
        tail = []
        for j, u in enumerate(us):
            k = u['kind']
            if k == 'seg':
                if blk is not None:
                    refuse(f"gen5 field {fname}: two blocks")
                blk = u
                tail = us[j + 1:]
                break
            if k == 'callblk':
                if j != len(us) - 1:
                    refuse(f"gen5 field {fname}: a unit after the call block")
                blk = u
                break
            steps.append(g5_step(u, regs, stk, frame, pfx, fl, i, fields))
        cls = fields[i][3]
        if cls == 'bytes':
            if blk is None or blk['kind'] != 'seg':
                refuse(f"gen5 field {fname}: byte field without a segment")
            # pre steps of a byte field: only stack stores (they write frame slots)
            if any(u['kind'] != 'st' or u['rB'] != 'rsp' for u in us[:us.index(blk)]):
                refuse(f"gen5 field {fname}: set-up before the segment other than stack stores")
            if not (len(tail) == 4 and [t['kind'] for t in tail] == ['ld', 'jmp', 'label', 'st']
                    and tail[0]['rB'] == 'rsp' and tail[0]['disp'] == blk['dS'] and tail[0].get('form') == 'v'
                    and tail[1]['jl'] == tail[2]['jd'] and tail[3]['rS'] == tail[0]['rD']
                    and tail[3]['rB'] == blk['rY'] and tail[0]['rD'] != blk['rY'] and tail[3]['disp'] == blk['fP']):
                refuse(f"gen5 field {fname}: pointer tail is not `mov dS(%rsp),%r; jmp; label; mov %r,fP(%rY)`")
            # segment effect: the spill area merged into one 24-byte existential, the low stack, pointer, return slot
            for a in area[1:]:
                stk[:] = [sl for sl in stk if not (sl[0] == 'at' and sl[1] == -frame + a)]
            setslot(stk, -frame, ('ex', 0))
            setlo(stk, ('ex', 1))
            setslot(stk, blk['dS'] - frame, ('ptr', bi))
            setslot(stk, -(frame + 8), ('ret', blk['jm'] + 1))
            exs = [24, 'lo']
            regs = {r: ('UNK',) for r in REGS16}
            regs[blk['rY']] = ('RCV', 0)
            fspec.append(dict(name=fname, shape='bytes', seg=f"{pfx}_{fname}_seg", dR=blk['dR'], dB=blk['dB'],
                              dS=blk['dS'], jm=blk['jm'], tail=[t['jd'] for t in tail], pre=steps))
            bi += 1
        elif cls == 'call':
            if blk is None or blk['kind'] != 'callblk':
                refuse(f"gen5 field {fname}: call field without a call block")
            want = dict(rax=('RCV', fields[i][2]), rbx=('BF', fields[i][1]), rcx=('IMM', 8))
            for r, w in want.items():
                if regs.get(r) != w:
                    refuse(f"gen5 field {fname}: at the call {r} = {regs.get(r)}, needed {w}")
            if has_rt:
                if any(sl[0] == 'at' and sl[1] == -frame + 8 for sl in stk):
                    setslot(stk, -frame + 8, ('ex', 0))
                    exs = [8, 'lo']
                else:
                    setslot(stk, -frame, ('ex', 0))
                    exs = [24, 'lo']
                setlo(stk, ('ex', 1))
            else:
                setslot(stk, -frame + 8, ('ex', 0))
                setslot(stk, -(frame + 16), ('ex', 1))
                exs = [8, 8]
            setslot(stk, -(frame + 8), ('ret', blk['jc'] + 1))
            regs = {r: ('UNK',) for r in REGS16}
            regs.update(rax=('ZERO',), rbx=('ZERO',))
            c = G5_CALLEES[blk['fn']]
            fspec.append(dict(name=fname, shape='call', callee=c[1], call=f"{pfx}_{fname}_call", jc=blk['jc'],
                              steps=steps))
        elif cls == 'u64':
            if blk is not None:
                refuse(f"gen5 field {fname}: inline uint64 field with a block")
            last = us[-1]
            if not (last['kind'] == 'st' and last['rB'] != 'rsp'):
                refuse(f"gen5 field {fname}: inline uint64 field does not end with its receiver store")
            fspec.append(dict(name=fname, shape='u64', steps=steps))
        else:
            refuse(f"gen5 field {fname}: class {cls}")
        if not fl_done_ok(us, cls):
            refuse(f"gen5 field {fname}: the field event is not the last unit")
        pc = us[-1]['e'] if cls != 'call' else blk['e']
        nxt = units[i + 1][0]['j'] if i + 1 < n else end
        if pc != nxt:
            refuse(f"gen5 field {fname}: ends at {pc}, the next unit starts at {nxt}")
        states.append(dict(pc=pc, done=i + 1, regs=facts(needs[i + 1], f'field {i + 2}' if i + 1 < n else 'epilogue'),
                           stk=freeze(stk), exs=list(exs)))
    if states[-1]['pc'] != epi['start']:
        refuse("gen5: epilogue does not start at the last boundary")
    # epilogue pre steps (loads of the two zero slots) and their slots
    if epi['form'] == 'ld':
        for r, d in epi['loads']:
            if getslot(stk, d - frame) != ('zero',):
                refuse(f"gen5 epilogue: `mov {d:#x}(%rsp),%{r}` reads a slot that is not zero")
        Z = '(0 : UInt64).toBitVec'
        epi['pre'] = [f"  apply kstep_ldv Reg64.{r} Reg64.rsp {d} _ (k + {epi['start'] + j}) (k + {epi['start'] + j + 1}) "
                      f"(win hk {epi['start'] + j} 1) (by rfl) (by rfl)\n    (s.regs.rsp.toBitVec - {frame}) "
                      f"{soff(d - frame)} {Z} {ADDR} _ _ _ (by rfl) (by ecancel)\n  kn"
                      for j, (r, d) in enumerate(epi['loads'])]
    post = freeze(stk)
    rej = g5_reject_spec(dirs, head, label_index)
    del regs0
    t = T(ns=pfx, C=args.const, Cq=args.const, go=args.type, L=None, same_as_prop=args.same_as_prop,
             same_as=args.same_as, callees=callees, fields=fl, st=st, stack=stack, pre=pre, rt=rt, gd=gd, frame=frame,
             exs=exs, post=post, states=states, headspec=head, fspec=fspec, epispec=epi, rejspec=rej)
    t.L = t.layout()
    return t


def fl_done_ok(us, cls):
    last = us[-1]
    if cls == 'call':
        return last['kind'] == 'callblk'
    return last['kind'] == 'st'


def g5_epi_spec(dirs, i, F, has_rt, has_call):
    """The three epilogue forms of the hand-over (contiguous, no nop): `add $F,%rsp; pop %rbp; retq` (rax = rbx = 0
    from the boundary facts), `mov d1(%rsp),%rax; mov d2(%rsp),%rbx` + that (two zero slots), and frame 0x20
    `xor %eax,%eax; xor %ebx,%ebx` + that (`decepi_seg`). Anything else: refuse."""
    ret = [f"add ${F:#x},%rsp", "pop %rbp", "retq"]
    if dirs[i:i + 3] == ret:
        return dict(form='n', F=F, add=i, start=i, reads=['rax', 'rbx'])
    m1 = re.fullmatch(r"mov (0x[0-9a-f]+)\(%rsp\),%rax", dirs[i]) if i < len(dirs) else None
    m2 = re.fullmatch(r"mov (0x[0-9a-f]+)\(%rsp\),%rbx", dirs[i + 1]) if i + 1 < len(dirs) else None
    if m1 and m2 and dirs[i + 2:i + 5] == ret:
        return dict(form='ld', F=F, add=i + 2, start=i, reads=[],
                    loads=[('rax', _hx(m1.group(1))), ('rbx', _hx(m2.group(1)))])
    if dirs[i:i + 2] == ["xor %eax,%eax", "xor %ebx,%ebx"] and dirs[i + 2:i + 5] == ret:
        if F != 0x20:
            refuse(f"gen5 epilogue: `xor` epilogue in frame {F:#x} (lemma decepi_seg: frame 0x20 only)")
        return dict(form='e20', F=F, add=i, start=i, reads=[])
    refuse(f"gen5 epilogue: directives {i}… {dirs[i:i + 5]} are none of the three epilogue forms")


def g5_step(u, regs, stk, frame, pfx, fl, cur, fields):
    """Render one GEN4 step theorem as an application in entry terms and update the register model."""
    k = u['kind']
    nm = f"{pfx}_s{u['jd']}"
    rterm = {('RCV',): lambda o: off('s.regs.rax.toBitVec', o), ('BF',): lambda o: off('s.regs.rbx.toBitVec', o)}

    def base_term(r):
        v = regs.get(r, ('UNK',))
        if v[0] in ('RCV', 'BF'):
            return rterm[(v[0],)](v[1]), v
        refuse(f"gen5: directive {u['jd']} `{u['text']}`: base {r} = {v} (not receiver / buffer)")

    def find(o):
        for sl in stk:
            if sl[0] == 'at' and sl[1] == o:
                return sl
        refuse(f"gen5: directive {u['jd']} `{u['text']}`: no stack chunk at entry offset {o}")
    if k == 'ld':
        rD, rB, d = u['rD'], u['rB'], u['disp']
        if rB == 'rsp':
            o = d - frame
            v = find(o)[2]
            if u['form'] == 'v':
                vt = {('reg', 'rax'): ('s.regs.rax.toBitVec', ('RCV', 0)), ('reg', 'rbx'): ('s.regs.rbx.toBitVec', ('BF', 0)),
                      ('zero',): ('(0 : UInt64).toBitVec', ('ZERO',))}.get(v)
                if vt is None:
                    refuse(f"gen5: directive {u['jd']} `{u['text']}`: value load of slot {v}")
                regs[rD] = vt[1]
                return (f"  apply {nm} k hk hf (s.regs.rsp.toBitVec - {frame}) {soff(o)} {vt[0]} {ADDR} _ _ _ (by rfl) (by ecancel)\n  kn")
            bs, hbs = _vterm_plain(v)
            regs[rD] = ('OPQ',)
            return (f"  apply {nm} k hk hf (s.regs.rsp.toBitVec - {frame}) {soff(o)} {ADDR} {bs} {hbs} _ _ _ (by rfl) (by ecancel)\n  kn")
        bt, bv = base_term(rB)
        if bv[0] != 'BF' or u['form'] != 'b':
            refuse(f"gen5: directive {u['jd']} `{u['text']}`: load through {rB} = {bv}")
        a = bv[1] + d
        if fields[cur][3] != 'u64' or a != fields[cur][1]:
            refuse(f"gen5: directive {u['jd']} `{u['text']}`: input load at SSZ offset {a}, field {fields[cur][0]} at {fields[cur][1]}")
        var = fl[cur][0]
        regs[rD] = ('IN', cur)
        return (f"  apply {nm} k hk hf {bt} {off('s.regs.rbx.toBitVec', a)} {ADDR0 if d == 0 else ADDR} {var} h{var} _ _ _ (by rfl) (by ecancel)\n  kn")
    if k == 'st':
        rS, rB, d = u['rS'], u['rB'], u['disp']
        v = regs.get(rS, ('UNK',))
        if rB == 'rsp':
            o = d - frame
            sl = find(o)
            bs, hbs = _vterm_plain(sl[2])
            nv = {('RCV', 0): ('reg', 'rax'), ('BF', 0): ('reg', 'rbx'), ('ZERO',): ('zero',)}.get(v)
            if nv is None:
                refuse(f"gen5: directive {u['jd']} `{u['text']}`: stack store of {v}")
            sl[2] = nv
            n = u['jd']
            return (f"  apply {nm} k hk hf (s.regs.rsp.toBitVec - {frame}) {soff(o)} {ADDR} {bs} {hbs} _ _ _ (by rfl) (by ecancel)\n"
                    f"  intro m{n} H{n}; kn; simp only [Reg64s.get64] at H{n}")
        bt, bv = base_term(rB)
        if bv[0] != 'RCV':
            refuse(f"gen5: directive {u['jd']} `{u['text']}`: store through {rB} = {bv}")
        a = bv[1] + d
        if fields[cur][3] != 'u64' or a != fields[cur][2] or v != ('IN', cur):
            refuse(f"gen5: directive {u['jd']} `{u['text']}`: receiver store of {v} at Go offset {a} (field "
                   f"{fields[cur][0]}: Go offset {fields[cur][2]})")
        var = fl[cur][0]
        return (f"  apply {nm} k hk hf {bt} {off('s.regs.rax.toBitVec', a)} {ADDR0 if d == 0 else ADDR} aN{cur} haN{cur} _ _ _\n"
                "    (by rfl) (by ecancel)\n  intro m' H\n  kn\n"
                f"  simp only [Reg64s.get64, toBytes_ofInt_ofBytes 64 8 rfl {var} h{var}] at H")
    if k == 'add':
        v = regs.get(u['rD'], ('UNK',))
        regs[u['rD']] = (v[0], v[1] + u['imm']) if v[0] in ('RCV', 'BF') else ('OPQ',)
        return f"  apply {nm} k hk hf\n  intro fl{u['jd']}; kn"
    if k == 'lea':
        if u['rB'] == 'rsp':
            refuse(f"gen5: directive {u['jd']} `{u['text']}`: address of a stack slot")
        v = regs.get(u['rB'], ('UNK',))
        regs[u['rD']] = (v[0], v[1] + u['disp']) if v[0] in ('RCV', 'BF') else ('OPQ',)
        return f"  apply {nm} k hk hf\n  kn"
    if k == 'movrr':
        regs[u['rD']] = regs.get(u['rS'], ('UNK',))
        return f"  apply {nm} k hk hf\n  kn"
    if k == 'movi':
        regs[u['rD']] = ('IMM', u['imm'] & 0xffffffff)
        return f"  apply {nm} k hk hf\n  kn"
    if k in ('jmp', 'label'):
        return f"  apply {nm} k hk hf"
    refuse(f"gen5: directive {u['jd']}: unit kind {k}")


def _vterm_plain(v):
    """Bytes term and length proof of a slot value (no existentials inside a field's own steps)."""
    k = v[0]
    if k == 'orig': return v[1], 'h' + v[1]
    if k == 'reg': return f'(Int.toBytes 8 s.regs.{v[1]}.toBitVec.toInt)', LEN
    if k == 'zero': return '(Int.toBytes 8 (0 : UInt64).toBitVec.toInt)', LEN
    if k == 'ret': return f'(Int.toBytes 8 (Host.addrOf (k + {v[1]})).toBitVec.toInt)', LEN
    if k == 'ex': return f'x{v[1]}', f'hx{v[1]}'
    if k == 'ptr': return f'(Int.toBytes 8 p{v[1] + 1}.toInt)', LEN
    refuse(f"gen5: slot value {v} inside a field's steps")
