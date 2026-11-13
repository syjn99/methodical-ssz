import Prysm.Checkpoint.CapacityReservedEncodeTail

/-! # OPT-R1 reserve encoder from `L_e5`: the reject tail (`len(Root) ≠ 32`). See `Prysm.Checkpoint.CapacityReservedEncodeTail`. -/

open Machine Runtime Prysm.Checkpoint.CapacityReserved.Code
variable [Host]

namespace Prysm.Checkpoint.CapacityReserved

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Tail from `L_e5`, `len(Root) ≠ 32`, `L + 8 ≤ C`: `(nil, ssz.ErrBytesLength)`; the epoch bytes are in
`b[L..L+8]` (written before the root length test, in the current block). -/
theorem Encode.tail_rej (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (rsp0 r140 rbp0 ra L C e0 e1 rl : UInt64) (hrl : rl ≠ 32) (rcv b p : BitVec 64)
    (e8 pre d0 t40 t30 : List UInt8) (he8 : e8.length = 8) (hd0 : d0.length = 8) (ht40 : t40.length = 16)
    (ht30 : t30.length = 16) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 152 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (hrax : s.regs.rax.toBitVec = rcv) (hrbx : s.regs.rbx.toBitVec = b) (hrcx : s.regs.rcx = L)
    (hrdx : s.regs.rdx = C)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
      ⋆ Eq (t30.At (rsp0.toBitVec - 48)) ⋆ Eq (t40.At (rsp0.toBitVec - 64))
      ⋆ Eq (e8.At (rcv + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (rcv + 24))
      ⋆ Eq (pre.At b) ⋆ Eq (d0.At (b + L.toBitVec))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrBytesLength_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R)
    (hcap : L.toNat + 8 ≤ C.toNat) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = rsp0 + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (t u : List UInt8), t.length = 8 ∧ u.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
          ⋆ Eq (u.At (rsp0.toBitVec - 48)) ⋆ Eq (e8.At (rsp0.toBitVec - 64)) ⋆ Eq (t.At (rsp0.toBitVec - 56))
          ⋆ Eq (e8.At (rcv + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (rcv + 24))
          ⋆ Eq (pre.At b) ⋆ Eq (e8.At (b + L.toBitVec))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrBytesLength_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 48)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx hrcx hrdx h_mem hrl ⊢
  subst rsp rbp r14 rcx rdx hrax hrbx
  have := L.toNat_lt_size; have := C.toNat_lt_size; have := rsp0.toNat_lt_size; simp only [UInt64.size] at *
  kat hk marshalSSZTo 48
  kat hk marshalSSZTo 49
  kat hk marshalSSZTo 50
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk marshalSSZTo 51
  kat hk marshalSSZTo 52
  kat hk marshalSSZTo 53
  kat hk marshalSSZTo 54
  kat hk marshalSSZTo 55
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp0.toBitVec - 152 + 88 = rsp0.toBitVec - 64 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t40 _ _ (by ecancel) (by exact ht40) (by decide)
  intro m3 H3
  kunfold
  kat hk marshalSSZTo 56
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp0.toBitVec - 64 + 16 = rsp0.toBitVec - 48 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t30 _ _ (by ecancel) (by exact ht30) (by decide)
  intro m4 H4
  kunfold
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp0.toBitVec - 64),
    show rsp0.toBitVec - 64 + 8 = rsp0.toBitVec - 56 by bv_omega] at H4
  kat hk marshalSSZTo 57
  apply store_step_at _ _ (rsp0.toBitVec - 64) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by checkpoint_addr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H5
  kunfold
  kat hk marshalSSZTo 58
  kat hk marshalSSZTo 59
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 72
  kat hk marshalSSZTo 72
  kat hk marshalSSZTo 73
  apply load_step_at _ _ (rsp0.toBitVec - 64) _ _ e8 _ _ (by checkpoint_addr) (by ecancel) (by exact he8)
  kunfold
  kat hk marshalSSZTo 74
  rw [Codec.add_mul_one]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m6 H6
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H6
  kunfold
  kat hk marshalSSZTo 75
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 p.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 76
  apply load_step_at _ _ (rax.toBitVec + 24) _ _ (Int.toBytes 8 rl.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk marshalSSZTo 77
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, Width.bits] at h
    exact hrl (UInt64.toBitVec_inj.mp (Codec.eq_32_of_sub_eq_zero _ h))
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 111
  kat hk marshalSSZTo 111
  kat hk marshalSSZTo 112
  rw [← ElfData.PrysmTarget.sszErrBytesLength_addr_eq]
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 113
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 114
  intro _
  kat hk marshalSSZTo 115
  intro _
  kat hk marshalSSZTo 116
  kat hk marshalSSZTo 117
  kat hk marshalSSZTo 118
  apply load_step_at _ _ (rsp0.toBitVec - 8) _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 119
  apply load_step_at _ _ rsp0.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?tt, ?uu, ?htt, ?huu, ?hmem⟩
  case hmem => ecancel
  case htt => simp [Int.toBytes_length]
  case huu => simp [Int.toBytes_length]
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; checkpoint_addr)

end Prysm.Checkpoint.CapacityReserved
