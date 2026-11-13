import Runtime.Contracts
import Machine.Step
import Machine.Labels
import Prysm.ElfData.CheckpointAndEpoch
import Prysm.SyncCommittee.DecodeLoop
import Prysm.HistoricalBatch.Code
import Prysm.HistoricalBatch.DecodeLoopLemmas

/-!
# `(*v1alpha1.HistoricalBatch).UnmarshalSSZ`: the BlockRoots loop (8192 iterations)

Loop head `L_a0` (directive 40). `sp` is the rsp of the body (`entry rsp − 64`). Frame slots relative to `sp`:
`sp + 72` receiver spill, `sp + 80` buf spill, `sp + 24` i + 1, `sp + 32` 32i, `sp + 40` i, `sp + 48` element
pointer, `sp` the 24-byte spill area of the callees, `sp − 8` the runtime call return slot, `sp − 8 − S` scratch.

`Decode.block_roots_iter` (one iteration, directives 40–77 and 36–39): 41–42 `cmp $0x2000; jge` not taken (i < 8192);
43–47 rsi = i, rax = 32i, rdi = 32(i + 1), r8 = i + 1; 49–50 `cmp %rax,%rdi; jb panicBounds` not taken;
51–53 save i, 32i, i + 1; 54–57 `makeslice(uint8, 0, 32)` (`MakesliceC`); 58 save p; 59–63 `memmove(p, buf + 32i, 32)`
(`MemmoveC`); 64–68 the bounds check `cmp %rsi,%rdi; jae panicBounds` with rsi = `BlockRoots.len` read from the
receiver (8192): not taken; 69–72 len and cap words of header i; 73–75 writeBarrier = 0; 76–77, 36–39 the pointer
word of header i, `rax = i + 1` (loaded from `sp + 24`).
Proof order: `Prysm.SyncCommittee.Decode.iter`, `Prysm.SyncCommittee.Decode.exit`, `Prysm.SyncCommittee.Decode.loop` (`Prysm/SyncCommittee/DecodeLoop.lean`); the step sequence is this decoder's own.
The macro `laddr` and the lemmas `jge_false512`, `Prysm.SyncCommittee.elementBlocks_snoc` are imported from the SyncCommittee proof.
-/

open Machine Runtime TestTarget Prysm.HistoricalBatch.Code
variable [Host]

namespace Prysm.HistoricalBatch

/-- The value that `shl $5` leaves in a 64-bit register, with Kraken's width term `Width.W64.bits` in the
shift instance (the form `kshl64` produces; `x <<< 5` at width `64` is not syntactically equal, and `ecancel` does
not unify the two). -/
scoped notation "shl5 " x:max => @HShiftLeft.hShiftLeft Width.W64.type Nat (BitVec 64)
  (@BitVec.instHShiftLeftNat Width.W64.bits) x 5

theorem Decode.block_roots_iter (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
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
      ⋆ Eq (pks.flatten.At bf)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 8192).At (recv + 8))
      ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps ++ Prysm.SyncCommittee.zz (24 * (8192 - i))).At A) ⋆ Prysm.SyncCommittee.elementBlocks ps (pks.take i)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 40) ∧ st.data.regs.rax.toNat = i + 1
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (l18' l20' l28' l30' spl' rslot' lo' : List UInt8), l18'.length = 8 ∧ l20'.length = 8
          ∧ l28'.length = 8 ∧ l30'.length = 8 ∧ spl'.length = 24 ∧ rslot'.length = 8 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At (sp + 72)) ⋆ Eq ((Int.toBytes 8 bf.toInt).At (sp + 80))
          ⋆ Eq (l18'.At (sp + 24)) ⋆ Eq (l20'.At (sp + 32)) ⋆ Eq (l28'.At (sp + 40)) ⋆ Eq (l30'.At (sp + 48))
          ⋆ Eq (spl'.At sp) ⋆ Eq (rslot'.At (sp - 8)) ⋆ Eq (lo'.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap (avail - 32)
          ⋆ Eq (pks.flatten.At bf)
          ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 8192).At (recv + 8))
          ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 (ps ++ [p]) ++ Prysm.SyncCommittee.zz (24 * (8192 - (i + 1)))).At A) ⋆ Prysm.SyncCommittee.elementBlocks (ps ++ [p]) (pks.take (i + 1))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 40)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrsp hrbp hr14 ⊢
  subst hrsp hrbp hr14
  have := rax.toNat_lt_size; simp only [UInt64.size] at *
  have hlt : i < pks.length := by omega
  have hpi : pks[i].length = 32 := hpk _ (List.getElem_mem hlt)
  rw [Decode.input_split bf pks hpks hpk i hi, Decode.array_split A ps i hi hps] at h_mem
  generalize hE : pks[i] = e at h_mem hpi
  kat hk unmarshalSSZ 40
  kat hk unmarshalSSZ 41
  kat hk unmarshalSSZ 42
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact Prysm.SyncCommittee.jge_false512 _ _ (by simp) (by simp; omega) h
  simp only [Effects.All]
  -- 43 rsi = i; 44 rax = 32i; 45 rdi = i + 1; 46 r8 = i + 1; 47 rdi = 32(i + 1); 48 nop; 49–50 jb not taken
  kat hk unmarshalSSZ 43
  kat hk unmarshalSSZ 44
  kshl64 5
  kat hk unmarshalSSZ 45
  kat hk unmarshalSSZ 46
  kat hk unmarshalSSZ 47
  kshl64 5
  kat hk unmarshalSSZ 48
  kat hk unmarshalSSZ 49
  kat hk unmarshalSSZ 50
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    (try simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.shiftLeft_eq] at h)
    simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at h; omega
  simp only [Effects.All]
  -- 51 save i; 52 save 32i; 53 save i + 1
  kat hk unmarshalSSZ 51
  apply store_step_at _ _ (sp + 40) _ _ _ l28 _ _ (by kaddr) (by ecancel) (by exact h28)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk unmarshalSSZ 52
  apply store_step_at _ _ (sp + 32) _ _ _ l20 _ _ (by kaddr) (by ecancel) (by exact h20)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk unmarshalSSZ 53
  apply store_step_at _ _ (sp + 24) _ _ _ l18 _ _ (by kaddr) (by ecancel) (by exact h18)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  -- 54–57 makeslice(uint8, 0, 32)
  kat hk unmarshalSSZ 54
  kat hk unmarshalSSZ 55
  intro _
  kat hk unmarshalSSZ 56
  kat hk unmarshalSSZ 57
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by kaddr) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 57 + 1)) 32 avail lo spl _
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
  kat hk unmarshalSSZ 58
  apply store_step_at _ _ (sp + 48) _ _ _ l30 _ _ (by kaddr) (by ecancel) (by exact h30)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk unmarshalSSZ 59
  apply load_step_at _ _ (sp + 32) _ _ (Int.toBytes 8 (shl5 rax.toBitVec).toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 60
  apply load_step_at _ _ (sp + 80) _ _ (Int.toBytes 8 bf.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 61
  kat hk unmarshalSSZ 62
  kat hk unmarshalSSZ 63
  apply store_step_at _ _ (sp - 8) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 57 + 1)).toBitVec.toInt) _ _
    (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  rw [show bf + (rax.toBitVec <<< 5) * 1#64 = bf + BitVec.ofNat 64 (32 * i) by laddr]
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 63 + 1)) e (List.replicate 32 0) stk3 _
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
  kat hk unmarshalSSZ 64
  apply load_step_at _ _ (sp + 72) _ _ (Int.toBytes 8 recv.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 65
  apply load_step_at _ _ (recv + 8) _ _ (Int.toBytes 8 8192) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 66
  apply load_step_at _ _ (sp + 40) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 67
  kat hk unmarshalSSZ 68
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rw [show Int.ofBytes (Int.toBytes 8 8192) = 8192 by decide] at h; omega
  simp only [Effects.All]
  -- 69 rsi = 3i; 70 load A; 71–72 len and cap of header i; 73–75 writeBarrier; 76 load p; 77 jmp L_8f
  kat hk unmarshalSSZ 69
  kat hk unmarshalSSZ 70
  apply load_step_at _ _ recv _ _ (Int.toBytes 8 A.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 71
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i) + 8) _ _ _ (Prysm.SyncCommittee.zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk unmarshalSSZ 72
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i) + 16) _ _ _ (Prysm.SyncCommittee.zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk unmarshalSSZ 73
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk unmarshalSSZ 74
  kat hk unmarshalSSZ 75
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk unmarshalSSZ 76
  apply load_step_at _ _ (sp + 48) _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 77
  klabel hk hf unmarshalSSZ 36
  kat hk unmarshalSSZ 36
  kat hk unmarshalSSZ 37
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i)) _ _ _ (Prysm.SyncCommittee.zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk unmarshalSSZ 38
  apply load_step_at _ _ (sp + 24) _ _ (Int.toBytes 8 (rax.toBitVec + 1).toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 39
  apply Eventually.done
  have e32 : Int.toBytes 8 (BitVec.toInt (32 : BitVec 64)) = Int.toBytes 8 32 := by decide
  simp only [e32] at H9
  refine ⟨rfl, ?_, rfl, rfl, rfl, rax3.toBitVec, Int.toBytes 8 (rax.toBitVec + 1).toInt,
    Int.toBytes 8 (shl5 rax.toBitVec).toInt, Int.toBytes 8 rax.toBitVec.toInt, Int.toBytes 8 rax3.toBitVec.toInt,
    spm3, Int.toBytes 8 (Host.addrOf (k + 63 + 1)).toBitVec.toInt, stk4, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, hspm3, Int.toBytes_length 8 _, hstk4, ?_⟩
  · show (rax.toBitVec + 1).toNat = i + 1
    simp [BitVec.toNat_add]; omega
  · dsimp only
    rw [Decode.input_split bf pks hpks hpk i hi, Decode.array_join A rax3.toBitVec ps i hi hps,
      List.take_succ_eq_append_getElem hlt, Prysm.SyncCommittee.elementBlocks_snoc ps (List.take i pks) _ _ (by simp [hps]; omega)]
    simp only [hE]
    ecancel

/-- Loop exit: at `L_a0` with rax = 8192 the `jge` is taken; the state reaches directive 86 (after `L_166`). -/
theorem Decode.block_roots_exit (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (P : MachineState → Prop) (s : MachineData) (hrax : s.regs.rax.toNat = 8192)
    (hP : ∀ f : StatusFlags, P ⟨⟨s.regs, s.zmms, f, s.dmem⟩, Host.addrOf (k + 86)⟩) :
    Eventually (step1 Host.exe) P ⟨s, Host.addrOf (k + 40)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrax hP ⊢
  have h8192 : rax = 8192 := UInt64.toNat_inj.mp (by rw [hrax]; rfl)
  subst h8192
  kat hk unmarshalSSZ 40
  kat hk unmarshalSSZ 41
  kat hk unmarshalSSZ 42
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 85
  kat hk unmarshalSSZ 85
  exact Eventually.done _ (hP _)

/-- **The BlockRoots loop**: from `L_a0` with i elements done (`i + j = 8192`) to directive 86 with all 8192 done. -/
theorem Decode.block_roots_loop (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (sp recv bf A : BitVec 64) (pks : List (List UInt8)) (hpks : pks.length = 8192)
    (hpk : ∀ e ∈ pks, e.length = 32) (rbp0 r140 : UInt64) (S : Nat)
    (Heap : Nat → DataMem → Prop) (R : DataMem → Prop)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    ∀ (j i : Nat) (ps : List (BitVec 64)) (l18 l20 l28 l30 spl rslot lo : List UInt8) (avail : Nat)
      (s : MachineData),
    i + j = 8192 → ps.length = i → l18.length = 8 → l20.length = 8 → l28.length = 8 → l30.length = 8 →
    spl.length = 24 → rslot.length = 8 → lo.length = S → 32 * j ≤ avail →
    s.regs.rax.toNat = i → s.regs.rsp = { toBitVec := sp } → s.regs.rbp = rbp0 → s.regs.r14 = r140 →
    (s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At (sp + 72)) ⋆ Eq ((Int.toBytes 8 bf.toInt).At (sp + 80))
      ⋆ Eq (l18.At (sp + 24)) ⋆ Eq (l20.At (sp + 32)) ⋆ Eq (l28.At (sp + 40)) ⋆ Eq (l30.At (sp + 48))
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At (sp - 8)) ⋆ Eq (lo.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap avail
      ⋆ Eq (pks.flatten.At bf)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 8192).At (recv + 8))
      ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps ++ Prysm.SyncCommittee.zz (24 * (8192 - i))).At A) ⋆ Prysm.SyncCommittee.elementBlocks ps (pks.take i)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 86) ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0
        ∧ st.data.regs.r14 = r140 ∧
        ∃ (ps' : List (BitVec 64)) (l18' l20' l28' l30' spl' rslot' lo' : List UInt8), ps'.length = 8192
          ∧ l18'.length = 8 ∧ l20'.length = 8 ∧ l28'.length = 8 ∧ l30'.length = 8 ∧ spl'.length = 24
          ∧ rslot'.length = 8 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At (sp + 72)) ⋆ Eq ((Int.toBytes 8 bf.toInt).At (sp + 80))
      ⋆ Eq (l18'.At (sp + 24)) ⋆ Eq (l20'.At (sp + 32)) ⋆ Eq (l28'.At (sp + 40)) ⋆ Eq (l30'.At (sp + 48))
      ⋆ Eq (spl'.At sp) ⋆ Eq (rslot'.At (sp - 8)) ⋆ Eq (lo'.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap (avail - 32 * j)
      ⋆ Eq (pks.flatten.At bf)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 8192).At (recv + 8))
      ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps' ++ Prysm.SyncCommittee.zz (24 * (8192 - 8192))).At A) ⋆ Prysm.SyncCommittee.elementBlocks ps' (pks.take 8192)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 40)⟩ := by
  intro j
  induction j with
  | zero =>
    intro i ps l18 l20 l28 l30 spl rslot lo avail s hij hps h18 h20 h28 h30 hspl hrs hlo _ hrax hrsp hrbp hr14 h_mem
    have hi : i = 8192 := by omega
    subst hi
    exact Decode.block_roots_exit k hk hf _ s hrax fun _ => ⟨rfl, hrsp, hrbp, hr14, ps, l18, l20, l28, l30, spl, rslot, lo,
      hps, h18, h20, h28, h30, hspl, hrs, hlo, by simpa using h_mem⟩
  | succ j ih =>
    intro i ps l18 l20 l28 l30 spl rslot lo avail s hij hps h18 h20 h28 h30 hspl hrs hlo hav hrax hrsp hrbp hr14 h_mem
    refine eventually_trans _ _ _ _ (Decode.block_roots_iter k hk hf sp recv bf A pks hpks hpk i (by omega) ps hps rbp0 r140
      l18 l20 l28 l30 spl rslot lo h18 h20 h28 h30 hspl hrs S hlo Heap avail (by omega) R s hrax hrsp hrbp hr14 h_mem
      hms hmm) ?_
    rintro ⟨d, pc⟩ ⟨hpc, h1, h2, h3, h4, p, l18', l20', l28', l30', spl', rslot', lo', g18, g20, g28, g30, gspl, grs,
      glo, Hm⟩
    dsimp only at hpc h1 h2 h3 h4 Hm
    subst hpc
    refine eventually_trans _ _ _ _ (ih (i + 1) (ps ++ [p]) l18' l20' l28' l30' spl' rslot' lo' (avail - 32) d
      (by omega) (by simp [hps]) g18 g20 g28 g30 gspl grs glo (by omega) h1 h2 h3 h4 Hm) ?_
    rintro st ⟨g1, g2, g3, g4, ps', m18, m20, m28, m30, mspl, mrs, mlo, q0, q1, q2, q3, q4, q5, q6, q7, Hm'⟩
    refine Eventually.done _ ⟨g1, g2, g3, g4, ps', m18, m20, m28, m30, mspl, mrs, mlo, q0, q1, q2, q3, q4, q5, q6, q7,
      ?_⟩
    rw [show avail - 32 * (j + 1) = avail - 32 - 32 * j by omega]
    exact Hm'

end Prysm.HistoricalBatch
