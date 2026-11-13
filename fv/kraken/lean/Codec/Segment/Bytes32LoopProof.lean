import Codec.Segment.Bytes32Loop

/-!
# Element loop with 32-byte elements: one iteration, the exit and the whole loop, for any count `n < 2^31`

Generalized once from `Prysm.HistoricalBatch.Decode.block_roots_iter`/`Decode.state_roots_iter`/`Decode.state_roots_loop` (same proof steps; the directive indices are block
offsets, the frame slots and receiver words are parameters with address equations, the input is at `bfs`).
The return slot keeps the value of the last `memmove` return address (`jS + 2`), as in `Decode.state_roots_loop`.
-/

open Machine Runtime Prysm.HistoricalBatch

namespace Codec.Segment

variable [Host]

/-- **One iteration** (`i < n`) from the loop head `jH` back to `jH`. -/
theorem v32_iter (n : Nat) (hn : n < 2 ^ 31) (lhead lexit lp1 lp2 lwb lback : String)
    (dI dD dI1 dP dB dR fL fP src : Int64) (jH jM jS jHd jT jB : Nat)
    (hB1 : (v32Head (OfNat.ofNat n) lhead lexit).IsInfixAt Host.prog jH)
    (hB2 : (v32Mid lp1 dI dD dI1 dP dB).IsInfixAt Host.prog jM)
    (hB3 : (v32Mm dR fL dI).IsInfixAt Host.prog jS)
    (hB4 : (v32Hdr lp2 fP).IsInfixAt Host.prog jHd)
    (hB5 : (v32Tail lwb lback dP).IsInfixAt Host.prog jT)
    (hB6 : (v32Back lback dI1).IsInfixAt Host.prog jB)
    (g1 : Glue (jH + 8) jM) (gs : GlueSrc (jM + 13) jS src) (g2 : Glue (jS + 5) jHd) (g3 : Glue (jHd + 7) jT)
    (g4 : Glue (jB + 3) jH) (hlb : label lback = Host.addrOf jB)
    (sp recv bf bfs A aI aD aI1 aP aB aR aL aA : BitVec 64)
    (haI : sp + dI.toBitVec = aI) (haD : sp + dD.toBitVec = aD) (haI1 : sp + dI1.toBitVec = aI1)
    (haP : sp + dP.toBitVec = aP) (haB : sp + dB.toBitVec = aB) (haR : sp + dR.toBitVec = aR)
    (haL : recv + fL.toBitVec = aL) (haA : recv + fP.toBitVec = aA) (hsrc : bf + src.toBitVec = bfs)
    (pks : List (List UInt8)) (hpks : pks.length = n) (hpk : ∀ e ∈ pks, e.length = 32)
    (i : Nat) (hi : i < n) (ps : List (BitVec 64)) (hps : ps.length = i)
    (rbp0 r140 : UInt64) (lI lD lI1 lP spl rslot lo : List UInt8)
    (hlI : lI.length = 8) (hlD : lD.length = 8) (hlI1 : lI1.length = 8) (hlP : lP.length = 8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 ≤ avail) (R : DataMem → Prop)
    (s : MachineData) (hrax : s.regs.rax.toNat = i) (hrsp : s.regs.rsp = { toBitVec := sp })
    (hrbp : s.regs.rbp = rbp0) (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (lI1.At aI1) ⋆ Eq (lD.At aD) ⋆ Eq (lI.At aI) ⋆ Eq (lP.At aP)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At (sp - 8)) ⋆ Eq (lo.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap avail
      ⋆ Eq (pks.flatten.At bfs)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At aA) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At aL)
      ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps ++ Prysm.SyncCommittee.zz (24 * (n - i))).At A) ⋆ Prysm.SyncCommittee.elementBlocks ps (pks.take i)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf jH ∧ st.data.regs.rax.toNat = i + 1
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (lI' lD' lI1' lP' spl' lo' : List UInt8), lI'.length = 8 ∧ lD'.length = 8
          ∧ lI1'.length = 8 ∧ lP'.length = 8 ∧ spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (lI1'.At aI1) ⋆ Eq (lD'.At aD) ⋆ Eq (lI'.At aI) ⋆ Eq (lP'.At aP)
          ⋆ Eq (spl'.At sp) ⋆ Eq ((Int.toBytes 8 (Host.addrOf (jS + 1 + 1)).toBitVec.toInt).At (sp - 8))
          ⋆ Eq (lo'.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap (avail - 32)
          ⋆ Eq (pks.flatten.At bfs)
          ⋆ Eq ((Int.toBytes 8 A.toInt).At aA) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At aL)
          ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 (ps ++ [p]) ++ Prysm.SyncCommittee.zz (24 * (n - (i + 1)))).At A) ⋆ Prysm.SyncCommittee.elementBlocks (ps ++ [p]) (pks.take (i + 1))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf jH⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrsp hrbp hr14 ⊢
  subst hrsp hrbp hr14
  have := rax.toNat_lt_size; simp only [UInt64.size] at *
  have hlt : i < pks.length := by omega
  have hpi : pks[i].length = 32 := hpk _ (List.getElem_mem hlt)
  rw [in_split 32 n (by omega) bfs pks hpks hpk i hi, arr_split n (by omega) 32 A ps i hi hps] at h_mem
  generalize hE : pks[i] = e at h_mem hpi
  -- head block: label, cmp $n / jge (not taken), rsi = i, rax = 32i, rdi = i + 1, r8 = i + 1, rdi = 32(i + 1)
  kat hB1 v32Head 0
  kat hB1 v32Head 1
  kat hB1 v32Head 2
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact Prysm.SyncCommittee.jge_false512 _ _ (by simp; omega) (by simp; omega) h
  simp only [Effects.All]
  kat hB1 v32Head 3
  kat hB1 v32Head 4
  kshl64 5
  kat hB1 v32Head 5
  kat hB1 v32Head 6
  kat hB1 v32Head 7
  kshl64 5
  apply glue_nop g1
  -- mid block: jb (not taken), three saves, makeslice(uint8, 0, 32), save p, rbx = buf + 32i
  kat hB2 v32Mid 0
  kat hB2 v32Mid 1
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    (try simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.shiftLeft_eq] at h)
    simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at h; omega
  simp only [Effects.All]
  kat hB2 v32Mid 2
  apply store_step_at _ _ aI _ _ _ lI _ _ (by rw [← haI]) (by ecancel) (by exact hlI)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hB2 v32Mid 3
  apply store_step_at _ _ aD _ _ _ lD _ _ (by rw [← haD]) (by ecancel) (by exact hlD)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hB2 v32Mid 4
  apply store_step_at _ _ aI1 _ _ _ lI1 _ _ (by rw [← haI1]) (by ecancel) (by exact hlI1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hB2 v32Mid 5
  kat hB2 v32Mid 6
  intro _
  kat hB2 v32Mid 7
  kat hB2 v32Mid 8
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by kaddr) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (jM + 8 + 1)) 32 avail lo spl _
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
  kat hB2 v32Mid 9
  apply store_step_at _ _ aP _ _ _ lP _ _ (by rw [← haP]) (by ecancel) (by exact hlP)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hB2 v32Mid 10
  apply load_step_at _ _ aD _ _ (Int.toBytes 8 (shl5 rax.toBitVec).toInt) _ _ (by rw [← haD]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hB2 v32Mid 11
  apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← haB]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hB2 v32Mid 12
  -- source offset (empty or `lea src(%rbx),%rbx`)
  refine glue_src gs ?_
  dsimp only
  rw [show bf + (rax.toBitVec <<< 5) * 1#64 + src.toBitVec = bfs + BitVec.ofNat 64 (32 * i) by
    rw [← hsrc]; laddr]
  -- memmove block: rcx = 32, memmove(p, bfs + 32i, 32), rdx = recv, rsi = len, rdi = i
  kat hB3 v32Mm 0
  kat hB3 v32Mm 1
  apply store_step_at _ _ (sp - 8) _ _ _ (Int.toBytes 8 (Host.addrOf (jM + 8 + 1)).toBitVec.toInt) _ _
    (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (jS + 1 + 1)) e (List.replicate 32 0) stk3 _
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
  kat hB3 v32Mm 2
  apply load_step_at _ _ aR _ _ (Int.toBytes 8 recv.toInt) _ _ (by rw [← haR]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hB3 v32Mm 3
  apply load_step_at _ _ aL _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by rw [← haL]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hB3 v32Mm 4
  apply load_step_at _ _ aI _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by rw [← haI]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  apply glue_nop g2
  -- header block: jae (not taken), rsi = 3i, rdi = A, len and cap words, writeBarrier
  kat hB4 v32Hdr 0
  kat hB4 v32Hdr 1
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hB4 v32Hdr 2
  kat hB4 v32Hdr 3
  apply load_step_at _ _ aA _ _ (Int.toBytes 8 A.toInt) _ _ (by rw [← haA]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hB4 v32Hdr 4
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i) + 8) _ _ _ (Prysm.SyncCommittee.zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hB4 v32Hdr 5
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i) + 16) _ _ _ (Prysm.SyncCommittee.zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hB4 v32Hdr 6
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  apply glue_nop g3
  -- tail block: jne (not taken), r9 = p, jmp L_back
  kat hB5 v32Tail 0
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hB5 v32Tail 1
  apply load_step_at _ _ aP _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by rw [← haP]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hB5 v32Tail 2
  rw [hlb]
  -- back block: label, pointer word of header i, rax = i + 1
  kat hB6 v32Back 0
  kat hB6 v32Back 1
  apply store_step_at _ _ (A + BitVec.ofNat 64 (24 * i)) _ _ _ (Prysm.SyncCommittee.zz 8) _ _ (by laddr) (by ecancel) (by rfl)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hB6 v32Back 2
  apply load_step_at _ _ aI1 _ _ (Int.toBytes 8 (rax.toBitVec + 1).toInt) _ _ (by rw [← haI1]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  apply glue_nop g4
  apply Eventually.done
  have e32 : Int.toBytes 8 (BitVec.toInt (32 : BitVec 64)) = Int.toBytes 8 32 := by decide
  simp only [e32] at H9
  refine ⟨rfl, ?_, rfl, rfl, rfl, rax3.toBitVec, Int.toBytes 8 rax.toBitVec.toInt,
    Int.toBytes 8 (shl5 rax.toBitVec).toInt, Int.toBytes 8 (rax.toBitVec + 1).toInt, Int.toBytes 8 rax3.toBitVec.toInt,
    spm3, stk4, Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    hspm3, hstk4, ?_⟩
  · show (rax.toBitVec + 1).toNat = i + 1
    simp [BitVec.toNat_add]; omega
  · dsimp only
    rw [in_split 32 n (by omega) bfs pks hpks hpk i hi, arr_join n (by omega) 32 A rax3.toBitVec ps i hi hps,
      List.take_succ_eq_append_getElem hlt, Prysm.SyncCommittee.elementBlocks_snoc ps (List.take i pks) _ _ (by simp [hps]; omega)]
    simp only [hE]
    ecancel

/-- **Loop exit**: at the head with rax = n the `jge` is taken; the state reaches the exit label `jE`. -/
theorem v32_exit (n : Nat) (hn : n < 2 ^ 31) (lhead lexit : String) (jH jE : Nat)
    (hB1 : (v32Head (OfNat.ofNat n) lhead lexit).IsInfixAt Host.prog jH) (hle : label lexit = Host.addrOf jE)
    (P : MachineState → Prop) (s : MachineData) (hrax : s.regs.rax.toNat = n)
    (hP : ∀ f : StatusFlags, P ⟨⟨s.regs, s.zmms, f, s.dmem⟩, Host.addrOf jE⟩) :
    Eventually (step1 Host.exe) P ⟨s, Host.addrOf jH⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrax hP ⊢
  obtain rfl : rax = UInt64.ofNat n := UInt64.toNat_inj.mp (by simp; omega)
  kat hB1 v32Head 0
  kat hB1 v32Head 1
  kat hB1 v32Head 2
  split
  case isFalse h =>
    exfalso; have hb : (UInt64.ofNat n).toBitVec = BitVec.ofNat 64 n := rfl
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hb] at h
  simp only [Effects.All]
  rw [hle]
  exact Eventually.done _ (hP _)

/-- **The element loop**: from the head with i elements done (`i + j = n`) to the exit label `jE` with all n done.
The return slot holds the last `memmove` return address (`jS + 2`) once one iteration has run (`0 < j`). -/
theorem v32_loop (n : Nat) (hn : n < 2 ^ 31) (lhead lexit lp1 lp2 lwb lback : String)
    (dI dD dI1 dP dB dR fL fP src : Int64) (jH jM jS jHd jT jB jE : Nat)
    (hB1 : (v32Head (OfNat.ofNat n) lhead lexit).IsInfixAt Host.prog jH)
    (hB2 : (v32Mid lp1 dI dD dI1 dP dB).IsInfixAt Host.prog jM)
    (hB3 : (v32Mm dR fL dI).IsInfixAt Host.prog jS)
    (hB4 : (v32Hdr lp2 fP).IsInfixAt Host.prog jHd)
    (hB5 : (v32Tail lwb lback dP).IsInfixAt Host.prog jT)
    (hB6 : (v32Back lback dI1).IsInfixAt Host.prog jB)
    (g1 : Glue (jH + 8) jM) (gs : GlueSrc (jM + 13) jS src) (g2 : Glue (jS + 5) jHd) (g3 : Glue (jHd + 7) jT)
    (g4 : Glue (jB + 3) jH) (hlb : label lback = Host.addrOf jB) (hle : label lexit = Host.addrOf jE)
    (sp recv bf bfs A aI aD aI1 aP aB aR aL aA : BitVec 64)
    (haI : sp + dI.toBitVec = aI) (haD : sp + dD.toBitVec = aD) (haI1 : sp + dI1.toBitVec = aI1)
    (haP : sp + dP.toBitVec = aP) (haB : sp + dB.toBitVec = aB) (haR : sp + dR.toBitVec = aR)
    (haL : recv + fL.toBitVec = aL) (haA : recv + fP.toBitVec = aA) (hsrc : bf + src.toBitVec = bfs)
    (pks : List (List UInt8)) (hpks : pks.length = n) (hpk : ∀ e ∈ pks, e.length = 32)
    (rbp0 r140 : UInt64) (S : Nat) (Heap : Nat → DataMem → Prop) (R : DataMem → Prop)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    ∀ (j i : Nat) (ps : List (BitVec 64)) (lI lD lI1 lP spl rslot lo : List UInt8) (avail : Nat) (s : MachineData),
    i + j = n → ps.length = i → lI.length = 8 → lD.length = 8 → lI1.length = 8 → lP.length = 8 →
    spl.length = 24 → rslot.length = 8 → lo.length = S → 32 * j ≤ avail →
    (0 < j ∨ rslot = (Int.toBytes 8 (Host.addrOf (jS + 1 + 1)).toBitVec.toInt)) →
    s.regs.rax.toNat = i → s.regs.rsp = { toBitVec := sp } → s.regs.rbp = rbp0 → s.regs.r14 = r140 →
    (s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (lI1.At aI1) ⋆ Eq (lD.At aD) ⋆ Eq (lI.At aI) ⋆ Eq (lP.At aP)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At (sp - 8)) ⋆ Eq (lo.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap avail
      ⋆ Eq (pks.flatten.At bfs)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At aA) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At aL)
      ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps ++ Prysm.SyncCommittee.zz (24 * (n - i))).At A) ⋆ Prysm.SyncCommittee.elementBlocks ps (pks.take i)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf jE ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0
        ∧ st.data.regs.r14 = r140 ∧
        ∃ (ps' : List (BitVec 64)) (lI' lD' lI1' lP' spl' lo' : List UInt8), ps'.length = n
          ∧ lI'.length = 8 ∧ lD'.length = 8 ∧ lI1'.length = 8 ∧ lP'.length = 8 ∧ spl'.length = 24
          ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (lI1'.At aI1) ⋆ Eq (lD'.At aD) ⋆ Eq (lI'.At aI) ⋆ Eq (lP'.At aP)
      ⋆ Eq (spl'.At sp) ⋆ Eq ((Int.toBytes 8 (Host.addrOf (jS + 1 + 1)).toBitVec.toInt).At (sp - 8)) ⋆ Eq (lo'.At (sp - 8 - BitVec.ofNat 64 S)) ⋆ Heap (avail - 32 * j)
      ⋆ Eq (pks.flatten.At bfs)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At aA) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At aL)
      ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps' ++ Prysm.SyncCommittee.zz (24 * (n - n))).At A) ⋆ Prysm.SyncCommittee.elementBlocks ps' (pks.take n)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf jH⟩ := by
  intro j
  induction j with
  | zero =>
    intro i ps lI lD lI1 lP spl rslot lo avail s hij hps hlI hlD hlI1 hlP hspl hrs hlo _ hr0 hrax hrsp hrbp hr14 h_mem
    have hi : i = n := by omega
    subst hi
    obtain hr0 | hr0 := hr0
    · exact absurd hr0 (Nat.lt_irrefl 0)
    subst hr0
    exact v32_exit _ hn lhead lexit jH jE hB1 hle _ s hrax fun _ => ⟨rfl, hrsp, hrbp, hr14, ps, lI, lD, lI1, lP, spl,
      lo, hps, hlI, hlD, hlI1, hlP, hspl, hlo, by simpa using h_mem⟩
  | succ j ih =>
    intro i ps lI lD lI1 lP spl rslot lo avail s hij hps hlI hlD hlI1 hlP hspl hrs hlo hav _ hrax hrsp hrbp hr14 h_mem
    refine eventually_trans _ _ _ _ (v32_iter n hn lhead lexit lp1 lp2 lwb lback dI dD dI1 dP dB dR fL fP src
      jH jM jS jHd jT jB hB1 hB2 hB3 hB4 hB5 hB6 g1 gs g2 g3 g4 hlb sp recv bf bfs A aI aD aI1 aP aB aR aL aA
      haI haD haI1 haP haB haR haL haA hsrc pks hpks hpk i (by omega) ps hps rbp0 r140 lI lD lI1 lP spl rslot lo
      hlI hlD hlI1 hlP hspl hrs S hlo Heap avail (by omega) R s hrax hrsp hrbp hr14 h_mem hms hmm) ?_
    rintro ⟨d, pc⟩ ⟨hpc, h1, h2, h3, h4, p, lI', lD', lI1', lP', spl', lo', g5, g6, g7, g8, gspl, glo, Hm⟩
    dsimp only at hpc h1 h2 h3 h4 Hm
    subst hpc
    refine eventually_trans _ _ _ _ (ih (i + 1) (ps ++ [p]) lI' lD' lI1' lP' spl' _ lo' (avail - 32) d
      (by omega) (by simp [hps]) g5 g6 g7 g8 gspl (Int.toBytes_length 8 _) glo (by omega) (Or.inr rfl)
      h1 h2 h3 h4 Hm) ?_
    rintro st ⟨q1, q2, q3, q4, ps', m1, m2, m3, m4, mspl, mlo, r0, r1, r2, r3, r4, r5, r6, Hm'⟩
    refine Eventually.done _ ⟨q1, q2, q3, q4, ps', m1, m2, m3, m4, mspl, mlo, r0, r1, r2, r3, r4, r5, r6, ?_⟩
    rw [show avail - 32 * (j + 1) = avail - 32 - 32 * j by omega]
    exact Hm'

end Codec.Segment
