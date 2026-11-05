import Fk.LuMarshal

/-!
# A `growslice` site under its contract (B2.5, C13)

ListU64.MarshalSSZTo, first append (`ssz.WriteOffset`, 4 bytes), slow path:
when `cap < len + 4` the code calls `runtime.growslice` (contract `GrowsliceC`,
1-byte elements) and continues at `L_53` (directive 25) with the new slice:
rbx = new ptr, rdx = len + 4, rdi = new cap ≥ len + 4, rax = receiver
(reloaded from its spill slot), and `dst[:len]` copied to the new block.
`lum_grow_site` runs directives 13–25 from the state after the capacity check.
Composing it with the rest of the function needs the fast-path loop under the
new capacity, or another growth per element; REPORT-1b (B2.5) gives the cost.
-/

open Fk Fk.Code
variable [Host]

theorem lg_112 (x : BitVec 64) : ({ toBitVec := x - 8#64 } + 8 : UInt64).toBitVec + 112 = x + 112 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem lg_rsp (x : UInt64) : ({ toBitVec := x.toBitVec - 8#64 } + 8 : UInt64) = x := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem lum_grow_site (k : Nat) (hk : ListU64MarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64MarshalSSZTo k)
    (pre : List UInt8) (s : MachineData) (hpre : pre.length = s.regs.rcx.toNat)
    (hrdx : s.regs.rdx.toNat = s.regs.rcx.toNat + 4)
    (sl rslot : List UInt8) (hsl : sl.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq (sl.At (s.regs.rsp.toBitVec + 112)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 8#64))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 8#64 - BitVec.ofNat 64 S))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hgs : GrowsliceC Heap (label "type__" + 47744).toBitVec 1 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 25) ∧ st.data.regs.rax = s.regs.rax
        ∧ st.data.regs.rdx = s.regs.rdx ∧ s.regs.rdx.toNat ≤ st.data.regs.rdi.toNat
        ∧ st.data.regs.rdi.toNat < 2 ^ 63 ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp ∧
        ∃ tail : List UInt8, pre.length + tail.length = st.data.regs.rdi.toNat ∧
        (Eq ((pre ++ tail).At st.data.regs.rbx.toBitVec) ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ R ⋆ fun _ => True)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 13)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hpre hrdx ⊢
  kat hk ListU64MarshalSSZTo 13
  apply store_step _ _ _ _ _ sl _ _ (by ecancel) (by exact hsl)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListU64MarshalSSZTo 14
  kat hk ListU64MarshalSSZTo 15
  kat hk ListU64MarshalSSZTo 16
  kat hk ListU64MarshalSSZTo 17
  kat hk ListU64MarshalSSZTo 18
  kat hk ListU64MarshalSSZTo 19
  kat hk ListU64MarshalSSZTo 20
  apply store_step_at _ _ (rsp.toBitVec - 8#64) _ _ _ rslot _ _ rfl (by dsimp only; ecancel) (by exact hrs)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  have := rcx.toNat_lt_size; have := rdx.toNat_lt_size; simp only [UInt64.size] at *
  have hpreC : (Eq ((Int.toBytes 8 (Host.addrOf (k + 20 + 1)).toBitVec.toInt).At (rsp.toBitVec - 8#64))
      ⋆ Eq (scratch.At (rsp.toBitVec - 8#64 - BitVec.ofNat 64 S)) ⋆ Eq (pre.At rbx.toBitVec) ⋆ Heap avail
      ⋆ (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At (rsp.toBitVec + 112)) ⋆ R)) m2 := by ecancel
  refine eventually_trans _ _ _ _ (hgs _ (Host.addrOf (k + 20 + 1)) pre scratch avail
    (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At (rsp.toBitVec + 112)) ⋆ R) rfl
    (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (4 : BitVec 64))).toNat ≤ rdx.toNat; simp; omega)
    (by show pre.length = 1 * (rdx.toNat - (BitVec.zeroExtend 64 (BitVec.truncate 32 (4 : BitVec 64))).toNat); simp; omega)
    hsc hpreC) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hrbx1, hcap1, hcap63, stk1, tail, av1, hstk1, htail, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hrbx1 hcap1 hcap63 Hm1 htail
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrbp1 hrbx1 hcap1 hcap63 Hm1 htail
  subst hrsp1 hrbp1 hrbx1
  kat hk ListU64MarshalSSZTo 21
  kat hk ListU64MarshalSSZTo 22
  kat hk ListU64MarshalSSZTo 23
  kat hk ListU64MarshalSSZTo 24
  rw [lg_112]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, tail, by simpa using htail, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp [Fk.ofInt_ofBytes_toBytes64]
  · rfl
  · simpa using hcap1
  · simpa using hcap63
  · exact lg_rsp rsp
  · rfl
  · dsimp only; exact sep_true (P := Eq ((pre ++ tail).At rax1.toBitVec) ⋆ Eq (pre.At rbx.toBitVec) ⋆ R) (by ecancel)
