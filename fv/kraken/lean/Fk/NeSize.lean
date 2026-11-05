import Fk.NeReject

/-!
# Nested.SizeSSZ on Kraken main

`ne_size_main`: with `c.L ≠ nil`, returns 28 + (4 + 8 len(c.L.L)) = 32 + 8n.
The `c.L == nil` path allocates a ListU64 (`runtime.newobject`) and is not
proved here. Every value the decoder produces has L ≠ nil
(`ne_accept_main`), and `MarshalSSZ` callers that build a Nested by hand may
leave it nil (REPORT-1b, remaining work).
Premises the Go caller provides: return address at rsp, saved-rbp slot,
the stack guard, the receiver's L pointer (≠ 0) and the L slice length.
-/

open Fk Fk.Code
variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem ne_size_main (k : Nat) (hk : NestedSizeSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedSizeSSZ k)
    (s : MachineData) (ra guard : UInt64) (fp : List UInt8) (hfp : fp.length = 8)
    (pl : BitVec 64) (hpl : pl ≠ 0) (n : Nat) (hn : n < 2 ^ 60) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pl.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (pl + 8)) ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toNat = 32 + 8 * n
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk NestedSizeSSZ 0
  kat hk NestedSizeSSZ 1
  kat hk NestedSizeSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedSizeSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk NestedSizeSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk NestedSizeSSZ 5
  kat hk NestedSizeSSZ 6
  kat hk NestedSizeSSZ 7
  apply load_step _ _ _ _ (Int.toBytes 8 pl.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedSizeSSZ 8
  split
  case isFalse h =>
    exfalso; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result] at h
    exact hpl h
  simp only [Effects.All]
  klabel hk hf NestedSizeSSZ 26
  kat hk NestedSizeSSZ 26
  kat hk NestedSizeSSZ 27
  apply load_step _ _ _ _ (Int.toBytes 8 pl.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedSizeSSZ 28
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedSizeSSZ 29
  kshl64 3
  kat hk NestedSizeSSZ 30
  kat hk NestedSizeSSZ 31
  kat hk NestedSizeSSZ 32
  rw [show (16 : BitVec 64) + (rsp.toBitVec - 8#64 - 16) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedSizeSSZ 33
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩
  · show (32 + BitVec.ofNat 64 n <<< 3).toNat = _
    simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · exact sep_true (by ecancel)
