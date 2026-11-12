import Fk.Block
import Fk.Labels

/-!
# FixedVec.UnmarshalSSZ element loop (W [4]uint64), on Kraken main

Loop head `L_a6` (directive 46).
-/

open Fk Fk.Code
variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem fv_iter (k : Nat) (hk : FixedVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh FixedVecUnmarshalSSZ k)
    (ws : List UInt8) (hws : ws.length = 8 * 4) (i : Nat) (hi : i < 4)
    (b c p : BitVec 64) (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = i) (hrcx : s.regs.rcx.toBitVec = b) (hrdx : s.regs.rdx.toBitVec = c)
    (sp bp rr : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp) (hr14 : s.regs.r14 = rr)
    (h_mem : s.dmem =⋆ Eq (ws.At (b + 32)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (c + 32))
      ⋆ Eq ((Int.toBytes 8 4).At (c + 40))
      ⋆ Eq ((ws.take (8 * i) ++ List.replicate (8 * (4 - i)) 0).At p) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 46) ∧ st.data.regs.rax.toNat = i + 1
        ∧ st.data.regs.rcx.toBitVec = b ∧ st.data.regs.rdx.toBitVec = c
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = rr
        ∧ (Eq (ws.At (b + 32)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 4).At (c + 40))
          ⋆ Eq ((ws.take (8 * (i + 1)) ++ List.replicate (8 * (4 - (i + 1))) 0).At p) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 46)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrcx hrdx hrsp hrbp hr14 ⊢
  subst hrcx hrdx hrsp hrbp hr14
  have := rax.toNat_lt_size
  simp only [UInt64.size] at *
  have hlen : ws.length < 2 ^ 64 := by omega
  rw [block_split ws (rcx.toBitVec + 32) (8 * i) (by omega) hlen, out_next ws 4 i hws hi,
    Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, List.length_replicate, hws, Nat.min_eq_left (show 8 * i ≤ 8 * 4 by omega)] at h_mem
  kat hk FixedVecUnmarshalSSZ 46
  kat hk FixedVecUnmarshalSSZ 47
  kat hk FixedVecUnmarshalSSZ 48
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact jge_false rax.toBitVec 4 (by simp) (by simp; omega) (by simpa using h)
  simp only [Effects.All]
  kat hk FixedVecUnmarshalSSZ 49
  kat hk FixedVecUnmarshalSSZ 50
  kshl64 3
  kat hk FixedVecUnmarshalSSZ 51
  kat hk FixedVecUnmarshalSSZ 52
  kat hk FixedVecUnmarshalSSZ 53
  kshl64 3
  kat hk FixedVecUnmarshalSSZ 54
  kat hk FixedVecUnmarshalSSZ 55
  kat hk FixedVecUnmarshalSSZ 56
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    (try simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.shiftLeft_eq] at h)
    simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at h; omega
  simp only [Effects.All]
  kat hk FixedVecUnmarshalSSZ 57
  apply load_step_at _ _ (rdx.toBitVec + 40) _ _ (Int.toBytes 8 4) _ _ (by bv_omega) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 4) = 4 by decide]
  kunfold
  kat hk FixedVecUnmarshalSSZ 58
  kat hk FixedVecUnmarshalSSZ 59
  rw [show rcx.toBitVec + rax.toBitVec * 8#64 + 32 = rcx.toBitVec + 32 + BitVec.ofNat 64 (8 * i) by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
  apply load_step _ _ _ _ ((ws.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  kunfold
  kat hk FixedVecUnmarshalSSZ 60
  kat hk FixedVecUnmarshalSSZ 61
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf FixedVecUnmarshalSSZ 42
  kat hk FixedVecUnmarshalSSZ 42
  kat hk FixedVecUnmarshalSSZ 43
  apply load_step_at _ _ (rdx.toBitVec + 32) _ _ (Int.toBytes 8 p.toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecUnmarshalSSZ 44
  rw [show p + rax.toBitVec * 8#64 = p + BitVec.ofNat 64 (8 * i) by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
  apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)
  intro m1 H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl _ (show ((ws.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1
  kunfold
  kat hk FixedVecUnmarshalSSZ 45
  apply Eventually.done
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · show (rax.toBitVec + 1).toNat = i + 1; simp [BitVec.toNat_add]; omega
  · dsimp only
    rw [← out_step ws 4 i hws hi, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
      block_split ws (rcx.toBitVec + 32) (8 * i) (by omega) hlen]
    simp only [List.length_take, List.length_replicate, List.length_drop, hws,
      Nat.min_eq_left (show 8 * i ≤ 8 * 4 by omega), Nat.min_eq_left (show 8 ≤ 8 * 4 - 8 * i by omega)]
    (try simp only [BitVec.ofNat_eq_ofNat] at H1 ⊢)
    ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem fv_exit (k : Nat) (hk : FixedVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh FixedVecUnmarshalSSZ k)
    (ws : List UInt8) (hws : ws.length = 8 * 4)
    (b c p : BitVec 64) (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = 4)
    (sp bp rr : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp) (hr14 : s.regs.r14 = rr)
    (h_mem : s.dmem =⋆ Eq (ws.At (b + 32)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (c + 32))
      ⋆ Eq ((Int.toBytes 8 4).At (c + 40))
      ⋆ Eq ((ws.take (8 * 4) ++ List.replicate (8 * (4 - 4)) 0).At p) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 63) ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = rr
        ∧ (Eq (ws.At (b + 32)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 4).At (c + 40))
          ⋆ Eq (ws.At p) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 46)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrsp hrbp hr14 ⊢
  subst hrsp hrbp hr14
  have hr : rax = 4 := UInt64.toNat_inj.mp (by simpa using hrax)
  subst hr
  kat hk FixedVecUnmarshalSSZ 46
  kat hk FixedVecUnmarshalSSZ 47
  kat hk FixedVecUnmarshalSSZ 48
  split
  case isFalse h => exfalso; exact h (by decide)
  simp only [Effects.All]
  klabel hk hf FixedVecUnmarshalSSZ 63
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.append_nil, List.take_of_length_le (by omega)] at h_mem
  exact h_mem

theorem fv_loop (k : Nat) (hk : FixedVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh FixedVecUnmarshalSSZ k)
    (ws : List UInt8) (hws : ws.length = 8 * 4)
    (b c p : BitVec 64) (R : DataMem → Prop) (sp bp rr : UInt64) :
    ∀ j i (s : MachineData), i + j = 4 →
    s.regs.rax.toNat = i → s.regs.rcx.toBitVec = b → s.regs.rdx.toBitVec = c → s.regs.rsp = sp → s.regs.rbp = bp → s.regs.r14 = rr →
    (s.dmem =⋆ Eq (ws.At (b + 32)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 4).At (c + 40))
      ⋆ Eq ((ws.take (8 * i) ++ List.replicate (8 * (4 - i)) 0).At p) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 63) ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = rr
        ∧ (Eq (ws.At (b + 32)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 4).At (c + 40))
          ⋆ Eq (ws.At p) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 46)⟩
  | 0, i, s, hij, hrax, _, _, hrsp, hrbp, hr14, h_mem => by
    have hin : i = 4 := by omega
    subst hin
    exact fv_exit k hk hf ws hws b c p R s hrax sp bp rr hrsp hrbp hr14 h_mem
  | j + 1, i, s, hij, hrax, hrcx, hrdx, hrsp, hrbp, hr14, h_mem => by
    refine eventually_trans _ _ _ _
      (fv_iter k hk hf ws hws i (by omega) b c p R s hrax hrcx hrdx sp bp rr hrsp hrbp hr14 h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h7, h6⟩
    dsimp only at hpc; subst hpc
    exact fv_loop k hk hf ws hws b c p R sp bp rr j (i + 1) s' (by omega) h1 h2 h3 h4 h5 h7 h6
