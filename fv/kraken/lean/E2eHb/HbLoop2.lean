import Runtime.Contracts
import Machine.Step
import Machine.Labels
import Prysm.ElfData.CheckpointAndEpoch
import Prysm.SyncCommittee.DecodeLoop
import E2eHb.Code
import E2eHb.HbLoop1

/-!
# `(*v1alpha1.HistoricalBatch).UnmarshalSSZ`: the StateRoots loop (8192 iterations)

Loop head `L_1c0` (directive 108). The frame is the one of `HbLoop1.lean`. `hb_iter2` covers directives 108–146
and 104–107. Differences from the BlockRoots loop: the receiver words are `StateRoots` (`recv + 24` pointer,
`recv + 32` len), the source is `buf + 262144 + 32i` (extra `lea 0x40000(%rbx),%rbx`, directive 130), and the
`nop` directives sit at 116 and 136 (not 48 and 74). Proof text: `HbLoop1.lean` with the directive indices,
these offsets and the `nop` steps changed.
The return slot: the last runtime call is the memmove of the last iteration (directive 132), so `hb_iter2` and
`hb_loop2` keep its value `k + 133` (`hb_loop1` leaves it unnamed; the accept statement needs it).
-/

open Machine Runtime TestTarget E2eHb.Code
variable [Host]

namespace E2eHb

theorem hb_iter2 (k : Nat) (hk : HbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh HbUnmarshal k)
    (sp recv bf A : BitVec 64) (pks : List (List UInt8)) (hpks : pks.length = 8192)
    (hpk : ∀ e ∈ pks, e.length = 32)
    (i : Nat) (hi : i < 8192) (ps : List (BitVec 64)) (hps : ps.length = i)
    (rbp0 r140 : UInt64) (l18 l20 l28 l30 spl rslot lo : List UInt8)
    (h18 : l18.length = 8) (h20 : l20.length = 8) (h28 : l28.length = 8) (h30 : l30.length = 8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 ≤ avail) (R : DataMem → Prop)
    (s : MachineData) (hrax : s.regs.rax.toNat = i) (hrsp : s.regs.rsp = { toBitVec := sp })
    (hrbp : s.regs.rbp = rbp0) (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At (sp + 72)) ⋆ Eq ((Int.toBytes 8 bf.toInt).At (sp + 80))
      ⋆ Eq (l18.At (sp + 24)) ⋆ Eq (l20.At (sp + 32)) ⋆ Eq (l28.At (sp + 40)) ⋆ Eq (l30.At (sp + 48))
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At (sp - 8)) ⋆ Eq (lo.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap avail
      ⋆ Eq (pks.flatten.At (bf + 262144))
      ⋆ Eq ((Int.toBytes 8 A.toInt).At (recv + 24)) ⋆ Eq ((Int.toBytes 8 8192).At (recv + 32))
      ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps ++ Prysm.SyncCommittee.zz (24 * (8192 - i))).At A) ⋆ Prysm.SyncCommittee.elementBlocks ps (pks.take i)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 108) ∧ st.data.regs.rax.toNat = i + 1
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (l18' l20' l28' l30' spl' lo' : List UInt8), l18'.length = 8 ∧ l20'.length = 8
          ∧ l28'.length = 8 ∧ l30'.length = 8 ∧ spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At (sp + 72)) ⋆ Eq ((Int.toBytes 8 bf.toInt).At (sp + 80))
          ⋆ Eq (l18'.At (sp + 24)) ⋆ Eq (l20'.At (sp + 32)) ⋆ Eq (l28'.At (sp + 40)) ⋆ Eq (l30'.At (sp + 48))
          ⋆ Eq (spl'.At sp) ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 133)).toBitVec.toInt).At (sp - 8)) ⋆ Eq (lo'.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap (avail - 32)
          ⋆ Eq (pks.flatten.At (bf + 262144))
          ⋆ Eq ((Int.toBytes 8 A.toInt).At (recv + 24)) ⋆ Eq ((Int.toBytes 8 8192).At (recv + 32))
          ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 (ps ++ [p]) ++ Prysm.SyncCommittee.zz (24 * (8192 - (i + 1)))).At A) ⋆ Prysm.SyncCommittee.elementBlocks (ps ++ [p]) (pks.take (i + 1))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 108)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrsp hrbp hr14 ⊢
  subst hrsp hrbp hr14
  have := rax.toNat_lt_size; simp only [UInt64.size] at *
  have hlt : i < pks.length := by omega
  have hpi : pks[i].length = 32 := hpk _ (List.getElem_mem hlt)
  rw [hbIn_split (bf + 262144) pks hpks hpk i hi, hbA_split A ps i hi hps] at h_mem
  generalize hE : pks[i] = e at h_mem hpi
  kat hk HbUnmarshal 108
  kat hk HbUnmarshal 109
  kat hk HbUnmarshal 110
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact Prysm.SyncCommittee.jge_false512 _ _ (by simp) (by simp; omega) h
  simp only [Effects.All]
  -- 43 rsi = i; 44 rax = 32i; 45 rdi = i + 1; 46 r8 = i + 1; 47 rdi = 32(i + 1); 48 nop; 49–50 jb not taken
  kat hk HbUnmarshal 111
  kat hk HbUnmarshal 112
  kshl64 5
  kat hk HbUnmarshal 113
  kat hk HbUnmarshal 114
  kat hk HbUnmarshal 115
  kshl64 5
  kat hk HbUnmarshal 116
  kat hk HbUnmarshal 117
  kat hk HbUnmarshal 118
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    (try simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.shiftLeft_eq] at h)
    simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at h; omega
  simp only [Effects.All]
  -- 51 save i; 52 save 32i; 53 save i + 1
  kat hk HbUnmarshal 119
  apply store_step_at _ _ (sp + 40) _ _ _ l28 _ _ (by kaddr) (by ecancel) (by exact h28)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk HbUnmarshal 120
  apply store_step_at _ _ (sp + 32) _ _ _ l20 _ _ (by kaddr) (by ecancel) (by exact h20)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk HbUnmarshal 121
  apply store_step_at _ _ (sp + 24) _ _ _ l18 _ _ (by kaddr) (by ecancel) (by exact h18)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  -- 54–57 makeslice(uint8, 0, 32)
  kat hk HbUnmarshal 122
  kat hk HbUnmarshal 123
  intro _
  kat hk HbUnmarshal 124
  kat hk HbUnmarshal 125
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by kaddr) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 125 + 1)) 32 avail lo spl _
    rfl (by simp) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega) hlo hspl
    (by dsimp only; rw [show sp - 8 + 8 = sp by bv_omega]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [show sp - 8 + 8 = sp by bv_omega] at Hm3
  simp only [Nat.one_mul] at Hm3
  -- 58 save p; 59 load 32i; 60 load buf; 61 rbx = buf + 32i; 62 rcx = 32; 63 memmove
  kat hk HbUnmarshal 126
  apply store_step_at _ _ (sp + 48) _ _ _ l30 _ _ (by kaddr) (by ecancel) (by exact h30)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk HbUnmarshal 127
  apply load_step_at _ _ (sp + 32) _ _ (Int.toBytes 8 (shl5 rax.toBitVec).toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk HbUnmarshal 128
  apply load_step_at _ _ (sp + 80) _ _ (Int.toBytes 8 bf.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk HbUnmarshal 129
  kat hk HbUnmarshal 130
  kat hk HbUnmarshal 131
  kat hk HbUnmarshal 132
  apply store_step_at _ _ (sp - 8) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 125 + 1)).toBitVec.toInt) _ _
    (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  rw [show bf + (rax.toBitVec <<< 5) * 1#64 + 262144 = bf + 262144 + BitVec.ofNat 64 (32 * i) by laddr]
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 132 + 1)) e (List.replicate 32 0) stk3 _
    (by rw [hpi]; rfl) (by simp [hpi]) hstk3 (by dsimp only; ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrbp4, stk4, hstk4, Hm4⟩
  dsimp only at hpc4 hrsp4 hr144 hrbp4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hr144 hrbp4 Hm4
  rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp4
  subst hrsp4 hr144 hrbp4
  -- 64 load recv; 65 load len = 8192; 66 load i; 67–68 bounds check (not taken)
  kat hk HbUnmarshal 133
  apply load_step_at _ _ (sp + 72) _ _ (Int.toBytes 8 recv.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk HbUnmarshal 134
  apply load_step_at _ _ (recv + 32) _ _ (Int.toBytes 8 8192) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk HbUnmarshal 135
  apply load_step_at _ _ (sp + 40) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk HbUnmarshal 136
  kat hk HbUnmarshal 137
  kat hk HbUnmarshal 138
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rw [show Int.ofBytes (Int.toBytes 8 8192) = 8192 by decide] at h; omega
  simp only [Effects.All]
  -- 69 rsi = 3i; 70 load A; 71–72 len and cap of header i; 73–75 writeBarrier; 76 load p; 77 jmp L_8f
  kat hk HbUnmarshal 139
  kat hk HbUnmarshal 140
  apply load_step_at _ _ (recv + 24) _ _ (Int.toBytes 8 A.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk HbUnmarshal 141
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i) + 8) _ _ _ (Prysm.SyncCommittee.zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk HbUnmarshal 142
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i) + 16) _ _ _ (Prysm.SyncCommittee.zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk HbUnmarshal 143
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk HbUnmarshal 144
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk HbUnmarshal 145
  apply load_step_at _ _ (sp + 48) _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk HbUnmarshal 146
  klabel hk hf HbUnmarshal 104
  kat hk HbUnmarshal 104
  kat hk HbUnmarshal 105
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i)) _ _ _ (Prysm.SyncCommittee.zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk HbUnmarshal 106
  apply load_step_at _ _ (sp + 24) _ _ (Int.toBytes 8 (rax.toBitVec + 1).toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk HbUnmarshal 107
  apply Eventually.done
  have e32 : Int.toBytes 8 (BitVec.toInt (32 : BitVec 64)) = Int.toBytes 8 32 := by decide
  simp only [e32] at H9
  rw [show k + 132 + 1 = k + 133 from rfl] at H9
  refine ⟨rfl, ?_, rfl, rfl, rfl, rax3.toBitVec, Int.toBytes 8 (rax.toBitVec + 1).toInt,
    Int.toBytes 8 (shl5 rax.toBitVec).toInt, Int.toBytes 8 rax.toBitVec.toInt, Int.toBytes 8 rax3.toBitVec.toInt,
    spm3, stk4, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, hspm3, hstk4, ?_⟩
  · show (rax.toBitVec + 1).toNat = i + 1
    simp [BitVec.toNat_add]; omega
  · dsimp only
    rw [hbIn_split (bf + 262144) pks hpks hpk i hi, hbA_join A rax3.toBitVec ps i hi hps,
      List.take_succ_eq_append_getElem hlt, Prysm.SyncCommittee.elementBlocks_snoc ps (List.take i pks) _ _ (by simp [hps]; omega)]
    simp only [hE]
    ecancel

/-- Loop exit: at `L_a0` with rax = 8192 the `jge` is taken; the state reaches directive 86 (after `L_166`). -/
theorem hb_exit2 (k : Nat) (hk : HbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh HbUnmarshal k)
    (P : MachineState → Prop) (s : MachineData) (hrax : s.regs.rax.toNat = 8192)
    (hP : ∀ f : StatusFlags, P ⟨⟨s.regs, s.zmms, f, s.dmem⟩, Host.addrOf (k + 155)⟩) :
    Eventually (step1 Host.exe) P ⟨s, Host.addrOf (k + 108)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrax hP ⊢
  have h8192 : rax = 8192 := UInt64.toNat_inj.mp (by rw [hrax]; rfl)
  subst h8192
  kat hk HbUnmarshal 108
  kat hk HbUnmarshal 109
  kat hk HbUnmarshal 110
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
  simp only [Effects.All]
  klabel hk hf HbUnmarshal 154
  kat hk HbUnmarshal 154
  exact Eventually.done _ (hP _)

/-- **The BlockRoots loop**: from `L_a0` with i elements done (`i + j = 8192`) to directive 86 with all 8192 done. -/
theorem hb_loop2 (k : Nat) (hk : HbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh HbUnmarshal k)
    (sp recv bf A : BitVec 64) (pks : List (List UInt8)) (hpks : pks.length = 8192)
    (hpk : ∀ e ∈ pks, e.length = 32) (rbp0 r140 : UInt64) (S : Nat)
    (Heap : Nat → DataMem → Prop) (R : DataMem → Prop)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    ∀ (j i : Nat) (ps : List (BitVec 64)) (l18 l20 l28 l30 spl rslot lo : List UInt8) (avail : Nat)
      (s : MachineData),
    i + j = 8192 → ps.length = i → l18.length = 8 → l20.length = 8 → l28.length = 8 → l30.length = 8 →
    spl.length = 24 → rslot.length = 8 → lo.length = S → 32 * j ≤ avail →
    (0 < j ∨ rslot = (Int.toBytes 8 (Host.addrOf (k + 133)).toBitVec.toInt)) →
    s.regs.rax.toNat = i → s.regs.rsp = { toBitVec := sp } → s.regs.rbp = rbp0 → s.regs.r14 = r140 →
    (s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At (sp + 72)) ⋆ Eq ((Int.toBytes 8 bf.toInt).At (sp + 80))
      ⋆ Eq (l18.At (sp + 24)) ⋆ Eq (l20.At (sp + 32)) ⋆ Eq (l28.At (sp + 40)) ⋆ Eq (l30.At (sp + 48))
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At (sp - 8)) ⋆ Eq (lo.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap avail
      ⋆ Eq (pks.flatten.At (bf + 262144))
      ⋆ Eq ((Int.toBytes 8 A.toInt).At (recv + 24)) ⋆ Eq ((Int.toBytes 8 8192).At (recv + 32))
      ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps ++ Prysm.SyncCommittee.zz (24 * (8192 - i))).At A) ⋆ Prysm.SyncCommittee.elementBlocks ps (pks.take i)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 155) ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0
        ∧ st.data.regs.r14 = r140 ∧
        ∃ (ps' : List (BitVec 64)) (l18' l20' l28' l30' spl' lo' : List UInt8), ps'.length = 8192
          ∧ l18'.length = 8 ∧ l20'.length = 8 ∧ l28'.length = 8 ∧ l30'.length = 8 ∧ spl'.length = 24
          ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At (sp + 72)) ⋆ Eq ((Int.toBytes 8 bf.toInt).At (sp + 80))
      ⋆ Eq (l18'.At (sp + 24)) ⋆ Eq (l20'.At (sp + 32)) ⋆ Eq (l28'.At (sp + 40)) ⋆ Eq (l30'.At (sp + 48))
      ⋆ Eq (spl'.At sp) ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 133)).toBitVec.toInt).At (sp - 8)) ⋆ Eq (lo'.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap (avail - 32 * j)
      ⋆ Eq (pks.flatten.At (bf + 262144))
      ⋆ Eq ((Int.toBytes 8 A.toInt).At (recv + 24)) ⋆ Eq ((Int.toBytes 8 8192).At (recv + 32))
      ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps' ++ Prysm.SyncCommittee.zz (24 * (8192 - 8192))).At A) ⋆ Prysm.SyncCommittee.elementBlocks ps' (pks.take 8192)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 108)⟩ := by
  intro j
  induction j with
  | zero =>
    intro i ps l18 l20 l28 l30 spl rslot lo avail s hij hps h18 h20 h28 h30 hspl hrs hlo _ hr0 hrax hrsp hrbp hr14
      h_mem
    have hi : i = 8192 := by omega
    subst hi
    obtain hr0 | hr0 := hr0
    · exact absurd hr0 (Nat.lt_irrefl 0)
    subst hr0
    exact hb_exit2 k hk hf _ s hrax fun _ => ⟨rfl, hrsp, hrbp, hr14, ps, l18, l20, l28, l30, spl, lo,
      hps, h18, h20, h28, h30, hspl, hlo, by simpa using h_mem⟩
  | succ j ih =>
    intro i ps l18 l20 l28 l30 spl rslot lo avail s hij hps h18 h20 h28 h30 hspl hrs hlo hav _ hrax hrsp hrbp hr14
      h_mem
    refine eventually_trans _ _ _ _ (hb_iter2 k hk hf sp recv bf A pks hpks hpk i (by omega) ps hps rbp0 r140
      l18 l20 l28 l30 spl rslot lo h18 h20 h28 h30 hspl hrs S hlo Heap avail (by omega) R s hrax hrsp hrbp hr14 h_mem
      hms hmm) ?_
    rintro ⟨d, pc⟩ ⟨hpc, h1, h2, h3, h4, p, l18', l20', l28', l30', spl', lo', g18, g20, g28, g30, gspl,
      glo, Hm⟩
    dsimp only at hpc h1 h2 h3 h4 Hm
    subst hpc
    refine eventually_trans _ _ _ _ (ih (i + 1) (ps ++ [p]) l18' l20' l28' l30' spl' _ lo' (avail - 32) d
      (by omega) (by simp [hps]) g18 g20 g28 g30 gspl (Int.toBytes_length 8 _) glo (by omega) (Or.inr rfl)
      h1 h2 h3 h4 Hm) ?_
    rintro st ⟨g1, g2, g3, g4, ps', m18, m20, m28, m30, mspl, mlo, q0, q1, q2, q3, q4, q5, q6, Hm'⟩
    refine Eventually.done _ ⟨g1, g2, g3, g4, ps', m18, m20, m28, m30, mspl, mlo, q0, q1, q2, q3, q4, q5, q6, ?_⟩
    rw [show avail - 32 * (j + 1) = avail - 32 - 32 * j by omega]
    exact Hm'

end E2eHb
