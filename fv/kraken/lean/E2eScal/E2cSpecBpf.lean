import E2eScal.Gen6F24BpfEnc
import E2eScal.F24BpfSpec
import Runtime.CopyModel

/-!
# BuilderPreferences encoder fast path (generated theorem) against the independent Desc (FLAT24 / H7, text of the unit E2-C emitter)

`bpf_e2c_spec_k`: for a receiver holding the Go layout of `g : PBpf` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `bpf_g6e_fast` writes at
`dst[len:len+8]` exactly the bytes of `serialize prysmBpfDesc g.toValue` (the Desc of the decoder's spec alignment).
Shape of `E2eScal.Bh.bh_e2e_marshal_spec_k`. Encoder fast path only (`len + 8 ≤ cap`, exact field
lengths). Emitted by the unit's evidence tool `e2cemit.py`, then built and kernel-checked.
-/

open Machine Runtime TestTarget E2e E2eScal Codec E2eScal.Gen6Enc E2eScal.F24Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.E2c

theorem bpf_e2c_enc_toList (g : PBpf) : (pbpfEnc g).toList = (uintBytes 8 g.maxExecutionPayment.toNat).toList := by
  simp only [pbpfEnc, Array.toList_append] <;> rfl

theorem bpf_e2c_split (a : BitVec 64) (A0 : List UInt8) (h0 : A0.length = 8) :
    Eq ((A0).At a) = Eq (A0.At a) := by
  rw []

set_option maxHeartbeats 4000000 in
theorem bpf_e2c_spec_k (k : Nat)
    (hk : BpfMarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh BpfMarshal k)
    (g : PBpf)
    (ast pre d0 : List UInt8)
    (hast : ast.length = 8)
    (hd0 : d0.length = 8)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 : List UInt8)
    (hfp : fp.length = 8)
    (hs2 : s2.length = 8)
    (ht40 : t40.length = 16)
    (ht24 : t24.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((uintBytes 8 g.maxExecutionPayment.toNat).toList.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hsp : 88 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    ∃ bs, serialize prysmBpfDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 8 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨pbpfEnc g, pbpf_serialize g, ?_⟩
  have hF0 : (uintBytes 8 g.maxExecutionPayment.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  refine eventually_mono (bpf_g6e_fast k hk hf ast (uintBytes 8 g.maxExecutionPayment.toNat).toList pre d0 hast hF0 hd0 s ra guard hpre fp s2 t40 t24 hfp hs2 ht40 ht24 R h_mem hguard hsp hcap hcap63)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [bpf_e2c_enc_toList, bpf_e2c_split _ _ hF0]
  try simp only [← Std.ExtHashMap.sep_assoc]  -- one output chunk: nothing to reassociate (FLAT24 attempt 2)
  generalize (uintBytes 8 g.maxExecutionPayment.toNat).toList = F0 at hm ⊢
  exact sep_true (by ecancel)

end E2eScal.E2c
