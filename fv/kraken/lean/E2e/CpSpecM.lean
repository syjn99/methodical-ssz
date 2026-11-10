import E2e.CpMarshal
import E2e.Spec
import Fk.RtCopy

/-!
# Encoder against EthLib, and SizeSSZ (prysm-e2e, INBOX 004 item 2)

- `cp_e2e_marshal_spec_k`: for a receiver holding the Go layout of `g : PCp`
  (`Epoch` = `uintBytes 8 g.epoch`, `Root` = `(p, 32, cap)` with `g.root` at `p`),
  the encoder fast path writes at `dst[len:len+40]` exactly the bytes of
  `serialize prysmCpDesc g.toValue` (the independent consensus-specs Desc). The
  full frame accounting is `cp_e2e_marshal_main`; this theorem states the output
  (`⋆ True` remainder of that conclusion).
- `cp_e2e_size_main`: `(*Checkpoint).SizeSSZ` (directives 0 label, 1 `mov $0x28,%eax`,
  2 `retq`) returns 40 with memory unchanged; `cp_e2e_size_spec`: 40 is the length
  of `serialize prysmCpDesc g.toValue`.
-/

open Fk E2e.Code EthLib.Serialization.Ssz
variable [Host]

namespace E2e

theorem pcp_enc_toList (g : PCp) : (pcpEnc g).toList = (uintBytes 8 g.epoch.toNat).toList ++ g.root.toList := by
  simp only [pcpEnc, Array.toList_append]; rfl

set_option maxHeartbeats 4000000 in
theorem cp_e2e_marshal_spec_k (k : Nat) (hk : CpMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshal k)
    (g : PCp) (cst cC ctl pre d0 d1 : List UInt8) (hcst : cst.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (p : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l24 l32 t40 t30 rslot : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (g.root.toList.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    ∃ bs, serialize prysmCpDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨pcpEnc g, pcp_serialize g, ?_⟩
  have he8 : (uintBytes 8 g.epoch.toNat).toList.length = 8 := by simp [Fv.uintBytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  refine eventually_mono (cp_e2e_marshal_main k hk hf cst _ cC ctl _ pre d0 d1 hcst he8 hcC hctl hroot hd0 hd1 p s ra
    guard hpre fp s2 l16 l24 l32 t40 t30 rslot hfp h2 hl16 hl24 hl32 ht40 ht30 hrs R S scratch hsc h_mem hguard hsp hcap
    hcap63 hmm) (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, t, u, scr, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [pcp_enc_toList,
    at_app _ g.root.toList (b := s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8) (by rw [he8]; rfl) (by simp [he8]), ← Std.ExtHashMap.sep_assoc]
  generalize (uintBytes 8 g.epoch.toNat).toList = E8 at hm ⊢
  generalize g.root.toList = Rt at hm ⊢
  exact sep_true (by ecancel)

theorem cp_e2e_size_main (k : Nat) (hk : CpSize.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 40 ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem ⊢
  kat hk CpSize 0
  kat hk CpSize 1
  kat hk CpSize 2
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact trivial
    | with_reducible rfl
    | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)

theorem cp_e2e_size_spec (g : PCp) : ∃ bs, serialize prysmCpDesc g.toValue = .ok bs ∧ bs.size = 40 :=
  ⟨pcpEnc g, pcp_serialize g, pcp_enc_size g⟩

end E2e
