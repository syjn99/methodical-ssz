module

public import Codec.SegmentAddress
public import Prysm.AttestationData.EncodeHeadRoot

@[expose] public section

/-!
# `(*v1alpha1.AttestationData).MarshalSSZTo`, fast path, segment 4: the Source encoder

    if a.Source == nil { a.Source = new(Checkpoint) }   // not taken
    if dst, err = a.Source.MarshalSSZTo(dst); err != nil { return nil, ssz.ErrMarshalSSZ… }

Directive indices of `Prysm.AttestationData.Code.marshalSSZTo` follow.
90: reload the receiver (rsp + 8).
91–92: `cmpq $0x0,0x30(%rdx); jne L_1b9` (taken).
107: `L_1b9`.
108: load rax = `Source`.
109: load rbx = `dst.ptr` (rsp − 48).
110: load rcx = `len + 48` (rsp − 120).
111: load rdi = `cap` (rsp − 128).
112: `callq Checkpoint.MarshalSSZTo`, through `Prysm.Checkpoint.Encode.fast_path_function_spec S`.
113–114: `test %rdi,%rdi; je L_264` (nil error, taken).
147: `L_264`.
Here `x` is the entry rsp, and the callee return slot is x − 192.
The callee frame is the 120 bytes below the return slot.
The `newobject` and write-barrier code of the nil branch is not on this path.
-/

open Machine Runtime Prysm.AttestationData.Code
variable [Host]

namespace Prysm.AttestationData

/-- The label `L_1b9` (directive 107) of the encoder. -/
theorem Encode.label_1b9 (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k) :
    label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_1b9" = Host.addrOf (k + 107) :=
  Machine.label_at' hk hf (j := 107)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero])
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)

/-- The label `L_264` (directive 147) of the encoder. -/
theorem Encode.label_264 (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k) :
    label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_264" = Host.addrOf (k + 147) :=
  Machine.label_at' hk hf (j := 147)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero])
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)

/-- The stack premises of a Checkpoint call with its return slot at x − 192. -/
theorem Encode.call_guard (x : BitVec 64) (g : Nat) (h : g + 312 < x.toNat) :
    g < ({ toBitVec := x - 192 } : UInt64).toNat ∧ 120 ≤ ({ toBitVec := x - 192 } : UInt64).toNat := by
  constructor <;> (show _ ≤ (x - 192).toNat; bv_omega)

/-- Segment 4 of the encoder fast path: from directive 90 to `L_264` (directive 147), through the Source encoder. -/
theorem Encode.source_call (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (S : Nat) (hcp : Prysm.Checkpoint.Encode.fast_path_function_spec S)
    (x rcv ps p d m cap : BitVec 64) (hps : ps ≠ 0) (guard : UInt64) (s : MachineData)
    (cst e8 cC ctl root pre d0 d1 rslot fp s2 l16 l24 l32 t40 t30 rs scratch : List UInt8)
    (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8) (hctl : ctl.length = 32)
    (hroot : root.length = 32) (hpre : pre.length = m.toNat) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (hrslot : rslot.length = 8) (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16)
    (hrs : rs.length = 8) (hsc : scratch.length = S)
    (hrsp : s.regs.rsp = { toBitVec := x - 184 })
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At (x + 8)) ⋆ Eq ((Int.toBytes 8 ps.toInt).At (rcv + 48))
      ⋆ Eq ((Int.toBytes 8 d.toInt).At (x - 48)) ⋆ Eq ((Int.toBytes 8 m.toInt).At (x - 120))
      ⋆ Eq ((Int.toBytes 8 cap.toInt).At (x - 128))
      ⋆ Eq (rslot.At (x - 192)) ⋆ Eq (fp.At (x - 200)) ⋆ Eq (s2.At (x - 176))
      ⋆ Eq (l16.At (x - 208)) ⋆ Eq (l24.At (x - 216)) ⋆ Eq (l32.At (x - 224)) ⋆ Eq (t30.At (x - 240))
      ⋆ Eq (t40.At (x - 256)) ⋆ Eq (rs.At (x - 312)) ⋆ Eq (scratch.At (x - 312 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At ps) ⋆ Eq (e8.At (ps + 8)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (ps + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (ps + 24)) ⋆ Eq (cC.At (ps + 32)) ⋆ Eq (ctl.At (ps + 40)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At d) ⋆ Eq (d0.At (d + m)) ⋆ Eq (d1.At (d + m + 8)) ⋆ R)
    (hguard : guard.toNat + 312 < x.toNat)
    (hcap : m.toNat + 40 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 147) ∧ st.data.regs.rax.toBitVec = d
        ∧ st.data.regs.rbx.toNat = m.toNat + 40 ∧ st.data.regs.rcx.toBitVec = cap
        ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u scr rs' : List UInt8), t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧ rs'.length = 8 ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At (x + 8)) ⋆ Eq ((Int.toBytes 8 ps.toInt).At (rcv + 48))
          ⋆ Eq ((Int.toBytes 8 d.toInt).At (x - 48)) ⋆ Eq ((Int.toBytes 8 m.toInt).At (x - 120))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (x - 128))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 113)).toBitVec.toInt).At (x - 192))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (x - 200))
          ⋆ Eq ((Int.toBytes 8 d.toInt).At (x - 176))
          ⋆ Eq ((Int.toBytes 8 d.toInt).At (x - 208)) ⋆ Eq ((Int.toBytes 8 cap.toInt).At (x - 216))
          ⋆ Eq ((Int.toBytes 8 (m + 40).toInt).At (x - 224)) ⋆ Eq (u.At (x - 240))
          ⋆ Eq (e8.At (x - 256)) ⋆ Eq (t.At (x - 248))
          ⋆ Eq (rs'.At (x - 312)) ⋆ Eq (scr.At (x - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At ps) ⋆ Eq (e8.At (ps + 8)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (ps + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 24)) ⋆ Eq (cC.At (ps + 32)) ⋆ Eq (ctl.At (ps + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At d) ⋆ Eq (e8.At (d + m)) ⋆ Eq (root.At (d + m + 8)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 90)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrsp ⊢
  subst rsp
  step_directive hk marshalSSZTo 90
  apply load_step_at _ _ (x + 8) _ _ (Int.toBytes 8 rcv.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 91
  apply load_step_at _ _ (rcv + 48) _ _ (Int.toBytes 8 ps.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 92
  split
  case isFalse h => exfalso; apply h; simp [CondCode.interp, StatusFlags.from_result]; exact hps
  simp only [Effects.All]
  rw [Encode.label_1b9 k hk hf]
  step_directive hk marshalSSZTo 107
  step_directive hk marshalSSZTo 108
  apply load_step_at _ _ (rcv + 48) _ _ (Int.toBytes 8 ps.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 109
  apply load_step_at _ _ (x - 48) _ _ (Int.toBytes 8 d.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 110
  apply load_step_at _ _ (x - 120) _ _ (Int.toBytes 8 m.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 111
  apply load_step_at _ _ (x - 128) _ _ (Int.toBytes 8 cap.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 112
  apply store_step_at _ _ (x - 192) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrslot)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  rw [show x - 184 - 8#64 = x - 192 by segment_addr]
  refine eventually_trans _ _ _ _ (hcp _ (Host.addrOf (k + 112 + 1)) guard p cst e8 cC ctl root pre d0 d1 fp s2
    l16 l24 l32 t40 t30 rs scratch _ hcst he8 hcC hctl hroot hd0 hd1 hpre hfp h2 hl16 hl24 hl32 ht40 ht30 hrs hsc
    (Encode.call_guard x _ hguard).1 (Encode.call_guard x _ hguard).2 hcap hcap63
    (by
      dsimp only
      rw [show x - 192 - 8 = x - 200 by segment_addr, show x - 192 + 16 = x - 176 by segment_addr,
        show x - 192 - 16 = x - 208 by segment_addr, show x - 192 - 24 = x - 216 by segment_addr,
        show x - 192 - 32 = x - 224 by segment_addr, show x - 192 - 48 = x - 240 by segment_addr,
        show x - 192 - 64 = x - 256 by segment_addr, show x - 192 - 120 = x - 312 by segment_addr]
      ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrcx5, hrdi5, hrsi5, hrsp5, hrbp5, hr145, t, u, scr, rs', ht, hu, hscr, hrs',
    Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrcx5 hrdi5 hrsi5 hrsp5 hrbp5 hr145 Hm5
  subst hpc5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145, r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrax5 hrbx5 hrcx5 hrdi5 hrsi5 hrsp5 hrbp5 hr145 Hm5
  rw [Encode.root_ret] at hrsp5
  subst rax5 rcx5 rdi5 rsp5 rbp5 r145
  step_directive hk marshalSSZTo 113
  intro _
  step_directive hk marshalSSZTo 114
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  rw [Encode.label_264 k hk hf]
  apply Eventually.done
  refine ⟨rfl, rfl, hrbx5, rfl, rfl, rfl, rfl, t, u, scr, rs', ht, hu, hscr, hrs', ?_⟩
  rw [show k + 112 + 1 = k + 113 from rfl,
    show x - 192 - 8 = x - 200 by segment_addr, show x - 192 + 16 = x - 176 by segment_addr,
    show x - 192 - 16 = x - 208 by segment_addr, show x - 192 - 24 = x - 216 by segment_addr,
    show x - 192 - 32 = x - 224 by segment_addr, show x - 192 - 48 = x - 240 by segment_addr,
    show x - 192 - 64 = x - 256 by segment_addr, show x - 192 - 56 = x - 248 by segment_addr,
    show x - 192 - 120 = x - 312 by segment_addr] at Hm5
  simp only [Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep] at Hm5
  dsimp only
  exact cast (congrFun (by ac_rfl) _) Hm5

end Prysm.AttestationData
