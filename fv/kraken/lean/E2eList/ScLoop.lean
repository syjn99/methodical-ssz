import Runtime.Contracts
import Machine.Step
import Machine.Labels
import Prysm.ElfData.CheckpointAndEpoch
import E2eList.Code
import E2eList.ScLemmas

/-!
# `(*v1alpha1.SyncCommittee).UnmarshalSSZ`: the 512-iteration element loop

Loop head `L_a0` (directive 40). `sp` is the rsp of the body (`entry rsp − 56`). Frame slots relative to `sp`:
`sp + 64` receiver spill, `sp + 72` buf spill, `sp + 24` i, `sp + 32` 3i, `sp + 40` element pointer, `sp` the 24-byte
spill area of the callees, `sp − 8` the runtime call return slot, `sp − 8 − S` the scratch bytes.

`sc_iter` (one iteration, directives 40–71 and 36–39):
41–42 `cmp $0x200,%rax; jge` not taken (i < 512); 43 save i; 44–48 `makeslice(uint8, 0, 48)` (`MakesliceC`);
49 save p; 50–55 `rbx = buf + 48·i`; 56–57 `memmove(p, buf + 48·i, 48)` (`MemmoveC`); 58–63 the bounds check
`cmp %rsi,%rdi; jae panicBounds` with rsi = `Pubkeys.len` read from the receiver (512) and rdi = i: proved not
taken; 64–67 the len and cap words of header i; 68–69 writeBarrier = 0; 70–71, 36–39 the pointer word of header i,
`rax = i + 1`.
-/

open Machine Runtime TestTarget E2eList.Code
variable [Host]

namespace E2eList

/-- Address equation by `toNat` and `omega` with products and shifts (the `kaddr` set plus `toNat_mul` and
`toNat_shiftLeft`). -/
macro "laddr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, UInt64.toNat_toBitVec, UInt64.toBitVec_add,
    UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

theorem sc_iter (k : Nat) (hk : ScUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh ScUnmarshal k)
    (sp recv bf A : BitVec 64) (pks : List (List UInt8)) (hpks : pks.length = 512)
    (hpk : ∀ e ∈ pks, e.length = 48)
    (i : Nat) (hi : i < 512) (ps : List (BitVec 64)) (hps : ps.length = i)
    (rbp0 r140 : UInt64) (l18 l20 l28 spl rslot lo : List UInt8)
    (h18 : l18.length = 8) (h20 : l20.length = 8) (h28 : l28.length = 8) (hspl : spl.length = 24)
    (hrs : rslot.length = 8) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 48 ≤ avail) (R : DataMem → Prop)
    (s : MachineData) (hrax : s.regs.rax.toNat = i) (hrsp : s.regs.rsp = { toBitVec := sp })
    (hrbp : s.regs.rbp = rbp0) (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At (sp + 64)) ⋆ Eq ((Int.toBytes 8 bf.toInt).At (sp + 72))
      ⋆ Eq (l18.At (sp + 24)) ⋆ Eq (l20.At (sp + 32)) ⋆ Eq (l28.At (sp + 40)) ⋆ Eq (spl.At sp)
      ⋆ Eq (rslot.At (sp - 8)) ⋆ Eq (lo.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap avail
      ⋆ Eq (pks.flatten.At bf)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At (recv + 8)) ⋆ Eq ((Int.toBytes 8 512).At (recv + 16))
      ⋆ Eq ((lvHdrs 48 ps ++ zz (24 * (512 - i))).At A) ⋆ lvElems ps (pks.take i)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 40) ∧ st.data.regs.rax.toNat = i + 1
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (l18' l20' l28' spl' rslot' lo' : List UInt8), l18'.length = 8 ∧ l20'.length = 8
          ∧ l28'.length = 8 ∧ spl'.length = 24 ∧ rslot'.length = 8 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At (sp + 64)) ⋆ Eq ((Int.toBytes 8 bf.toInt).At (sp + 72))
          ⋆ Eq (l18'.At (sp + 24)) ⋆ Eq (l20'.At (sp + 32)) ⋆ Eq (l28'.At (sp + 40)) ⋆ Eq (spl'.At sp)
          ⋆ Eq (rslot'.At (sp - 8)) ⋆ Eq (lo'.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap (avail - 48)
          ⋆ Eq (pks.flatten.At bf)
          ⋆ Eq ((Int.toBytes 8 A.toInt).At (recv + 8)) ⋆ Eq ((Int.toBytes 8 512).At (recv + 16))
          ⋆ Eq ((lvHdrs 48 (ps ++ [p]) ++ zz (24 * (512 - (i + 1)))).At A) ⋆ lvElems (ps ++ [p]) (pks.take (i + 1))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 40)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrsp hrbp hr14 ⊢
  subst hrsp hrbp hr14
  have := rax.toNat_lt_size; simp only [UInt64.size] at *
  have hlt : i < pks.length := by omega
  have hpi : pks[i].length = 48 := hpk _ (List.getElem_mem hlt)
  rw [scIn_split bf pks hpks hpk i hi, scA_split A ps i hi hps] at h_mem
  generalize hE : pks[i] = e at h_mem hpi
  kat hk ScUnmarshal 40
  kat hk ScUnmarshal 41
  kat hk ScUnmarshal 42
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact jge_false512 _ _ (by simp) (by simp; omega) h
  simp only [Effects.All]
  kat hk ScUnmarshal 43
  apply store_step_at _ _ (sp + 24) _ _ _ l18 _ _ (by kaddr) (by ecancel) (by exact h18)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ScUnmarshal 44
  kat hk ScUnmarshal 45
  intro _
  kat hk ScUnmarshal 46
  kat hk ScUnmarshal 47
  kat hk ScUnmarshal 48
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by kaddr) (by ecancel) (by exact hrs)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 48 + 1)) 48 avail lo spl _
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
  -- 49 save p; 50 load i; 51 3i; 52 save 3i; 53 48i; 54 load buf; 55 rbx = buf + 48i; 56 rcx = 48; 57 memmove
  kat hk ScUnmarshal 49
  apply store_step_at _ _ (sp + 40) _ _ _ l28 _ _ (by kaddr) (by ecancel) (by exact h28)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk ScUnmarshal 50
  apply load_step_at _ _ (sp + 24) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk ScUnmarshal 51
  kat hk ScUnmarshal 52
  apply store_step_at _ _ (sp + 32) _ _ _ l20 _ _ (by kaddr) (by ecancel) (by exact h20)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk ScUnmarshal 53
  kshl64 4
  kat hk ScUnmarshal 54
  apply load_step_at _ _ (sp + 72) _ _ (Int.toBytes 8 bf.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk ScUnmarshal 55
  kat hk ScUnmarshal 56
  kat hk ScUnmarshal 57
  apply store_step_at _ _ (sp - 8) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 48 + 1)).toBitVec.toInt) _ _
    (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  rw [show bf + (rax.toBitVec + rax.toBitVec * 2#64) <<< 4 * 1#64 = bf + BitVec.ofNat 64 (48 * i) by laddr]
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 57 + 1)) e (List.replicate 48 0) stk3 _
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
  -- 58 load recv; 59 load len = 512; 60 load i; 62–63 bounds check (not taken)
  kat hk ScUnmarshal 58
  apply load_step_at _ _ (sp + 64) _ _ (Int.toBytes 8 recv.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk ScUnmarshal 59
  apply load_step_at _ _ (recv + 16) _ _ (Int.toBytes 8 512) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ScUnmarshal 60
  apply load_step_at _ _ (sp + 24) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk ScUnmarshal 61
  kat hk ScUnmarshal 62
  kat hk ScUnmarshal 63
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rw [show Int.ofBytes (Int.toBytes 8 512) = 512 by decide] at h; omega
  simp only [Effects.All]
  -- 64 load A; 65 load 3i; 66–67 len and cap of header i; 68–69 writeBarrier; 70 load p; 71 jmp L_91
  kat hk ScUnmarshal 64
  apply load_step_at _ _ (recv + 8) _ _ (Int.toBytes 8 A.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk ScUnmarshal 65
  apply load_step_at _ _ (sp + 32) _ _ (Int.toBytes 8 (rax.toBitVec + rax.toBitVec * 2#64).toInt) _ _ (by kaddr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk ScUnmarshal 66
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i) + 8) _ _ _ (zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk ScUnmarshal 67
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i) + 16) _ _ _ (zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk ScUnmarshal 68
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk ScUnmarshal 69
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ScUnmarshal 70
  apply load_step_at _ _ (sp + 40) _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk ScUnmarshal 71
  klabel hk hf ScUnmarshal 36
  kat hk ScUnmarshal 36
  kat hk ScUnmarshal 37
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i)) _ _ _ (zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk ScUnmarshal 38
  kat hk ScUnmarshal 39
  apply Eventually.done
  have e48 : Int.toBytes 8 (BitVec.toInt (48 : BitVec 64)) = Int.toBytes 8 48 := by decide
  simp only [e48] at H9
  refine ⟨rfl, ?_, rfl, rfl, rfl, rax3.toBitVec, Int.toBytes 8 rax.toBitVec.toInt,
    Int.toBytes 8 (rax.toBitVec + rax.toBitVec * 2#64).toInt, Int.toBytes 8 rax3.toBitVec.toInt, spm3,
    Int.toBytes 8 (Host.addrOf (k + 57 + 1)).toBitVec.toInt, stk4, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, hspm3, Int.toBytes_length 8 _, hstk4, ?_⟩
  · show (rax.toBitVec + 1).toNat = i + 1
    simp [BitVec.toNat_add]; omega
  · dsimp only
    rw [scIn_split bf pks hpks hpk i hi, scA_join A rax3.toBitVec ps i hi hps,
      List.take_succ_eq_append_getElem hlt, lvElems_snoc ps (List.take i pks) _ _ (by simp [hps]; omega)]
    simp only [hE]
    ecancel

/-- Loop exit: at `L_a0` with rax = 512 the `jge` is taken; the state reaches directive 81 (after `L_156`). -/
theorem sc_exit (k : Nat) (hk : ScUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh ScUnmarshal k)
    (P : MachineState → Prop) (s : MachineData) (hrax : s.regs.rax.toNat = 512)
    (hP : ∀ f : StatusFlags, P ⟨⟨s.regs, s.zmms, f, s.dmem⟩, Host.addrOf (k + 81)⟩) :
    Eventually (step1 Host.exe) P ⟨s, Host.addrOf (k + 40)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrax hP ⊢
  have h512 : rax = 512 := UInt64.toNat_inj.mp (by rw [hrax]; rfl)
  subst h512
  kat hk ScUnmarshal 40
  kat hk ScUnmarshal 41
  kat hk ScUnmarshal 42
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
  simp only [Effects.All]
  klabel hk hf ScUnmarshal 80
  kat hk ScUnmarshal 80
  exact Eventually.done _ (hP _)

/-- **The element loop**: from `L_a0` with i elements done (`i + j = 512`) to directive 81 with all 512 done. -/
theorem sc_loop (k : Nat) (hk : ScUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh ScUnmarshal k)
    (sp recv bf A : BitVec 64) (pks : List (List UInt8)) (hpks : pks.length = 512)
    (hpk : ∀ e ∈ pks, e.length = 48) (rbp0 r140 : UInt64) (S : Nat)
    (Heap : Nat → DataMem → Prop) (R : DataMem → Prop)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    ∀ (j i : Nat) (ps : List (BitVec 64)) (l18 l20 l28 spl rslot lo : List UInt8) (avail : Nat) (s : MachineData),
    i + j = 512 → ps.length = i → l18.length = 8 → l20.length = 8 → l28.length = 8 → spl.length = 24 →
    rslot.length = 8 → lo.length = S → 48 * j ≤ avail →
    s.regs.rax.toNat = i → s.regs.rsp = { toBitVec := sp } → s.regs.rbp = rbp0 → s.regs.r14 = r140 →
    (s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At (sp + 64)) ⋆ Eq ((Int.toBytes 8 bf.toInt).At (sp + 72))
      ⋆ Eq (l18.At (sp + 24)) ⋆ Eq (l20.At (sp + 32)) ⋆ Eq (l28.At (sp + 40)) ⋆ Eq (spl.At sp)
      ⋆ Eq (rslot.At (sp - 8)) ⋆ Eq (lo.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap (avail)
      ⋆ Eq (pks.flatten.At bf)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At (recv + 8)) ⋆ Eq ((Int.toBytes 8 512).At (recv + 16))
      ⋆ Eq ((lvHdrs 48 ps ++ zz (24 * (512 - i))).At A) ⋆ lvElems ps (pks.take i)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 81) ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0
        ∧ st.data.regs.r14 = r140 ∧
        ∃ (ps' : List (BitVec 64)) (l18' l20' l28' spl' rslot' lo' : List UInt8), ps'.length = 512
          ∧ l18'.length = 8 ∧ l20'.length = 8 ∧ l28'.length = 8 ∧ spl'.length = 24 ∧ rslot'.length = 8
          ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At (sp + 64)) ⋆ Eq ((Int.toBytes 8 bf.toInt).At (sp + 72))
      ⋆ Eq (l18'.At (sp + 24)) ⋆ Eq (l20'.At (sp + 32)) ⋆ Eq (l28'.At (sp + 40)) ⋆ Eq (spl'.At sp)
      ⋆ Eq (rslot'.At (sp - 8)) ⋆ Eq (lo'.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap (avail - 48 * j)
      ⋆ Eq (pks.flatten.At bf)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At (recv + 8)) ⋆ Eq ((Int.toBytes 8 512).At (recv + 16))
      ⋆ Eq ((lvHdrs 48 ps' ++ zz (24 * (512 - 512))).At A) ⋆ lvElems ps' (pks.take 512)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 40)⟩ := by
  intro j
  induction j with
  | zero =>
    intro i ps l18 l20 l28 spl rslot lo avail s hij hps h18 h20 h28 hspl hrs hlo _ hrax hrsp hrbp hr14 h_mem
    have hi : i = 512 := by omega
    subst hi
    exact sc_exit k hk hf _ s hrax fun _ => ⟨rfl, hrsp, hrbp, hr14, ps, l18, l20, l28, spl, rslot, lo,
      hps, h18, h20, h28, hspl, hrs, hlo, by simpa using h_mem⟩
  | succ j ih =>
    intro i ps l18 l20 l28 spl rslot lo avail s hij hps h18 h20 h28 hspl hrs hlo hav hrax hrsp hrbp hr14 h_mem
    refine eventually_trans _ _ _ _ (sc_iter k hk hf sp recv bf A pks hpks hpk i (by omega) ps hps rbp0 r140
      l18 l20 l28 spl rslot lo h18 h20 h28 hspl hrs S hlo Heap avail (by omega) R s hrax hrsp hrbp hr14 h_mem hms hmm) ?_
    rintro ⟨d, pc⟩ ⟨hpc, h1, h2, h3, h4, p, l18', l20', l28', spl', rslot', lo', g18, g20, g28, gspl, grs, glo, Hm⟩
    dsimp only at hpc h1 h2 h3 h4 Hm
    subst hpc
    refine eventually_trans _ _ _ _ (ih (i + 1) (ps ++ [p]) l18' l20' l28' spl' rslot' lo' (avail - 48) d (by omega)
      (by simp [hps]) g18 g20 g28 gspl grs glo (by omega) h1 h2 h3 h4 Hm) ?_
    rintro st ⟨g1, g2, g3, g4, ps', m18, m20, m28, mspl, mrs, mlo, q0, q1, q2, q3, q4, q5, q6, Hm'⟩
    refine Eventually.done _ ⟨g1, g2, g3, g4, ps', m18, m20, m28, mspl, mrs, mlo, q0, q1, q2, q3, q4, q5, q6, ?_⟩
    rw [show avail - 48 * (j + 1) = avail - 48 - 48 * j by omega]
    exact Hm'

end E2eList
