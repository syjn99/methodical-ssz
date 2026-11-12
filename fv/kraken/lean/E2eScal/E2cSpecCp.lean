import E2eScal.Gen6CpEnc
import E2e.Spec
import Fk.RtCopy

/-!
# Checkpoint encoder fast path (generated theorem) against the independent Desc (unit E2-C)

`cp_e2c_spec_k`: for a receiver holding the Go layout of `g : PCp` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `cp_g6e_fast` writes at
`dst[len:len+40]` exactly the bytes of `serialize prysmCpDesc g.toValue` (the Desc of the decoder's spec alignment).
Shape of `E2eScal.Bh.bh_e2e_marshal_spec_k`. Encoder fast path only (`len + 40 ≤ cap`, exact field
lengths). Emitted by the unit's evidence tool `e2cemit.py`, then built and kernel-checked.
-/

open Fk E2e E2eScal E2eScal.Gen6Enc E2e.Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.E2c

theorem cp_e2c_enc_toList (g : PCp) : (pcpEnc g).toList = (uintBytes 8 g.epoch.toNat).toList ++ g.root.toList := by
  simp only [pcpEnc, Array.toList_append] <;> rfl

theorem cp_e2c_split (a : BitVec 64) (A0 A1 : List UInt8) (h0 : A0.length = 8) (h1 : A1.length = 32) :
    Eq ((A0 ++ A1).At a) = Eq (A0.At a) ⋆ Eq (A1.At (a + 8)) := by
  rw [at_app A0 _ (b := a + 8) (by rw [h0]; rfl) (by simp [h0, h1])]

set_option maxHeartbeats 4000000 in
theorem cp_e2c_spec_k (k : Nat)
    (hk : CpMarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh CpMarshal k)
    (g : PCp)
    (ast c1 pre d0 d1 : List UInt8)
    (hast : ast.length = 8)
    (hc1 : c1.length = 8)
    (hd0 : d0.length = 8)
    (hd1 : d1.length = 32)
    (p1 : BitVec 64)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l24 l32 t64 t48 rslot : List UInt8)
    (hfp : fp.length = 8)
    (hs2 : s2.length = 8)
    (hl16 : l16.length = 8)
    (hl24 : l24.length = 8)
    (hl32 : l32.length = 8)
    (ht64 : t64.length = 16)
    (ht48 : t48.length = 16)
    (hrslot : rslot.length = 8)
    (R : DataMem → Prop)
    (S : Nat)
    (scratch : List UInt8)
    (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (g.root.toList.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
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
  have hF0 : (uintBytes 8 g.epoch.toNat).toList.length = 8 := by simp [Fv.uintBytes_size]
  have hF1 : g.root.toList.length = 32 := by simp
  refine eventually_mono (cp_g6e_fast k hk hf ast (uintBytes 8 g.epoch.toNat).toList c1 (g.root.toList) pre d0 d1 hast hF0 hc1 hF1 hd0 hd1 p1 s ra guard hpre fp s2 l16 l24 l32 t64 t48 rslot hfp hs2 hl16 hl24 hl32 ht64 ht48 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [cp_e2c_enc_toList, cp_e2c_split _ _ _ hF0 hF1]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize (uintBytes 8 g.epoch.toNat).toList = F0 at hm ⊢
  generalize g.root.toList = F1 at hm ⊢
  exact sep_true (by ecancel)

end E2eScal.E2c
