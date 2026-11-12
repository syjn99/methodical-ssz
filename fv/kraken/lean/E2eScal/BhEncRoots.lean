import TestTarget.ListU64DecodeRejectCall
import E2e.CpMarshal
import E2eScal.BhCode

/-!
# Real Prysm `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo`, fast path, root blocks and epilogue

Hand proof (continues `E2eScal.BhEncHead`). Directive indices of `E2eScal.BhCode.BhMarshal`:

* `bh_enc_b` 62–89 + `runtime.memmove`: `len(ParentRoot)` check (62–65), capacity (66–68, `jae` taken), spills
  of the slice pointer (rsp − 16), the new length (rsp − 96) and the capacity (rsp − 104), the call.
* `bh_enc_c` 90–117 + `memmove`: the receiver is reloaded from rsp + 8; `len(StateRoot)` (90–93), capacity
  (94–98, `jb` not taken), 99–100 + `L_1d7` 111–114 (the capacity goes to rsp − 96, the new length to
  rsp − 104), the call.
* `bh_enc_d` 118–147 + `memmove`: the same for BodyRoot (length at rsp − 104, capacity at rsp − 96).
* `bh_enc_e` 148–155: reload of the result slice, `xor`, `add $0x98,%rsp`, `pop %rbp`, `retq`.

`runtime.memmove` (contract `MemmoveC S`) keeps rsp, rbp and r14 only, so each segment after a call starts
from a state whose other registers are arbitrary and reads its values from the frame. Each segment names
only the memory it touches; the rest is the frame `R`. `rsp` is the entry rsp of the function; the values
`recv` (receiver), `dst` (slice pointer), `v` (length before the block) and `cap` are parameters.
-/

open Machine Runtime TestTarget E2eScal.BhCode
variable [Host]

namespace E2eScal.Bh

theorem bhm_slot (x : BitVec 64) : x - 8#64 - 152 - 8#64 = x - 168 := by bv_omega

/-- `runtime.memmove` returned: rsp is the frame base again. -/
theorem bhm_ret (x : BitVec 64) : ({ toBitVec := x - 168 } + 8 : UInt64) = { toBitVec := x - 8#64 - 152 } := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- ParentRoot segment: directive 62 to the return of the first `memmove` (directive 90): ParentRoot appended. -/
theorem bh_enc_b (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (r1 e1 : List UInt8) (hr1 : r1.length = 32) (he1 : e1.length = 32)
    (s : MachineData) (rsp : UInt64) (recv dst v cap p1 : BitVec 64)
    (l16 l96 l104 rslot scratch : List UInt8)
    (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 8#64 - 152 })
    (hrax : s.regs.rax = { toBitVec := recv }) (hrbx : s.regs.rbx = { toBitVec := dst })
    (hr8 : s.regs.r8 = { toBitVec := v }) (hrdi : s.regs.rdi = { toBitVec := cap })
    (h_mem : s.dmem =⋆ Eq (l16.At (rsp.toBitVec - 16)) ⋆ Eq (l96.At (rsp.toBitVec - 96))
      ⋆ Eq (l104.At (rsp.toBitVec - 104))
      ⋆ Eq (rslot.At (rsp.toBitVec - 168)) ⋆ Eq (scratch.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (recv + 24)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 32))
      ⋆ Eq (r1.At p1) ⋆ Eq (e1.At (dst + v)) ⋆ R)
    (hcap : v.toNat + 32 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 90) ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16)) ⋆ Eq ((Int.toBytes 8 (v + 32).toInt).At (rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt).At (rsp.toBitVec - 168))
          ⋆ Eq (scr.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (recv + 24)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 32))
          ⋆ Eq (r1.At p1) ⋆ Eq (r1.At (dst + v)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 62)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrax hrbx hr8 hrdi h_mem ⊢
  subst hrsp hrax hrbx hr8 hrdi
  have := v.isLt; have := cap.isLt
  kat hk BhMarshal 62
  apply load_step_at _ _ (recv + 24) _ _ (Int.toBytes 8 p1.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 63
  apply load_step_at _ _ (recv + 32) _ _ (Int.toBytes 8 32) _ _ (by eaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk BhMarshal 64
  kat hk BhMarshal 65
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk BhMarshal 66
  kat hk BhMarshal 67
  kat hk BhMarshal 68
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf BhMarshal 82
  kat hk BhMarshal 82
  kat hk BhMarshal 83
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l16 _ _ (by eaddr) (by ecancel) (by exact hl16)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BhMarshal 84
  apply store_step_at _ _ (rsp.toBitVec - 96) _ _ _ l96 _ _ (by eaddr) (by ecancel) (by exact hl96)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BhMarshal 85
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ l104 _ _ (by eaddr) (by ecancel) (by exact hl104)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BhMarshal 86
  kat hk BhMarshal 87
  kat hk BhMarshal 88
  kat hk BhMarshal 89
  apply store_step_at _ _ (rsp.toBitVec - 168) _ _ _ rslot _ _ (bhm_slot _) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  rw [bhm_slot] at *
  rw [E2e.cpm_mul] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 89 + 1)) r1 e1 scratch _
    (by rw [hr1]; rfl) (by rw [hr1, he1]) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1', pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  apply Eventually.done
  refine ⟨hpc1, ?grsp, hrbp1, hr141, stk1, hstk1, ?hmem⟩
  case grsp => exact hrsp1.trans (bhm_ret _)
  case hmem =>
    rw [show k + 89 + 1 = k + 90 from rfl] at Hm1
    first | ecancel | (simp only [Std.ExtHashMap.sep_emp] at Hm1; ecancel)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- StateRoot segment: directive 90 to the return of the second `memmove` (directive 118): StateRoot appended. On entry the length is at rsp − 96 and the capacity at rsp − 104; on exit they are swapped. -/
theorem bh_enc_c (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (rr ee : List UInt8) (hrr : rr.length = 32) (hee : ee.length = 32)
    (s : MachineData) (rsp : UInt64) (recv dst v cap p2 : BitVec 64)
    (rslot scratch : List UInt8) (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 8#64 - 152 })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
      ⋆ Eq ((Int.toBytes 8 v.toInt).At (rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 104))
      ⋆ Eq (rslot.At (rsp.toBitVec - 168)) ⋆ Eq (scratch.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (recv + 48)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 56))
      ⋆ Eq (rr.At p2) ⋆ Eq (ee.At (dst + v)) ⋆ R)
    (hcap : v.toNat + 32 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 118) ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (v + 32).toInt).At (rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 118)).toBitVec.toInt).At (rsp.toBitVec - 168))
          ⋆ Eq (scr.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (recv + 48)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 56))
          ⋆ Eq (rr.At p2) ⋆ Eq (rr.At (dst + v)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 90)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst hrsp
  have := v.isLt; have := cap.isLt
  kat hk BhMarshal 90
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 recv.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 91
  apply load_step_at _ _ (recv + 48) _ _ (Int.toBytes 8 p2.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 92
  apply load_step_at _ _ (recv + 56) _ _ (Int.toBytes 8 32) _ _ (by eaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk BhMarshal 93
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk BhMarshal 94
  apply load_step_at _ _ (rsp.toBitVec - 96) _ _ (Int.toBytes 8 v.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 95
  kat hk BhMarshal 96
  apply load_step_at _ _ (rsp.toBitVec - 104) _ _ (Int.toBytes 8 cap.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 97
  kat hk BhMarshal 98
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  kat hk BhMarshal 99
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 dst.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 100
  klabel hk hf BhMarshal 111
  kat hk BhMarshal 111
  kat hk BhMarshal 112
  apply store_step_at _ _ (rsp.toBitVec - 96) _ _ _ (Int.toBytes 8 v.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BhMarshal 113
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ (Int.toBytes 8 cap.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BhMarshal 114
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ (Int.toBytes 8 dst.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BhMarshal 115
  kat hk BhMarshal 116
  kat hk BhMarshal 117
  apply store_step_at _ _ (rsp.toBitVec - 168) _ _ _ rslot _ _ (bhm_slot _) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  rw [bhm_slot] at *
  try rw [BitVec.add_comm v dst] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 117 + 1)) rr ee scratch _
    (by rw [hrr]; rfl) (by rw [hrr, hee]) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1', pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  apply Eventually.done
  refine ⟨hpc1, ?grsp, hrbp1, hr141, stk1, hstk1, ?hmem⟩
  case grsp => exact hrsp1.trans (bhm_ret _)
  case hmem =>
    rw [show k + 117 + 1 = k + 118 from rfl] at Hm1
    first | ecancel | (simp only [Std.ExtHashMap.sep_emp] at Hm1; ecancel)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- BodyRoot segment: directive 118 to the return of the third `memmove` (directive 148): BodyRoot appended. On entry the length is at rsp − 104 and the capacity at rsp − 96; they stay there. -/
theorem bh_enc_d (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (rr ee : List UInt8) (hrr : rr.length = 32) (hee : ee.length = 32)
    (s : MachineData) (rsp : UInt64) (recv dst v cap p3 : BitVec 64)
    (rslot scratch : List UInt8) (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 8#64 - 152 })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
      ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 v.toInt).At (rsp.toBitVec - 104))
      ⋆ Eq (rslot.At (rsp.toBitVec - 168)) ⋆ Eq (scratch.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (recv + 72)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 80))
      ⋆ Eq (rr.At p3) ⋆ Eq (ee.At (dst + v)) ⋆ R)
    (hcap : v.toNat + 32 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 148) ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (v + 32).toInt).At (rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 148)).toBitVec.toInt).At (rsp.toBitVec - 168))
          ⋆ Eq (scr.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (recv + 72)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 80))
          ⋆ Eq (rr.At p3) ⋆ Eq (rr.At (dst + v)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 118)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst hrsp
  have := v.isLt; have := cap.isLt
  kat hk BhMarshal 118
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 recv.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 119
  apply load_step_at _ _ (recv + 72) _ _ (Int.toBytes 8 p3.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 120
  apply load_step_at _ _ (recv + 80) _ _ (Int.toBytes 8 32) _ _ (by eaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk BhMarshal 121
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk BhMarshal 122
  apply load_step_at _ _ (rsp.toBitVec - 104) _ _ (Int.toBytes 8 v.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 123
  kat hk BhMarshal 124
  apply load_step_at _ _ (rsp.toBitVec - 96) _ _ (Int.toBytes 8 cap.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 125
  kat hk BhMarshal 126
  kat hk BhMarshal 127
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  kat hk BhMarshal 128
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 dst.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 129
  klabel hk hf BhMarshal 140
  kat hk BhMarshal 140
  kat hk BhMarshal 141
  apply store_step_at _ _ (rsp.toBitVec - 96) _ _ _ (Int.toBytes 8 cap.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BhMarshal 142
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ (Int.toBytes 8 v.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BhMarshal 143
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ (Int.toBytes 8 dst.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BhMarshal 144
  kat hk BhMarshal 145
  kat hk BhMarshal 146
  kat hk BhMarshal 147
  apply store_step_at _ _ (rsp.toBitVec - 168) _ _ _ rslot _ _ (bhm_slot _) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  rw [bhm_slot] at *
  try rw [BitVec.add_comm v dst] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 147 + 1)) rr ee scratch _
    (by rw [hrr]; rfl) (by rw [hrr, hee]) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1', pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  apply Eventually.done
  refine ⟨hpc1, ?grsp, hrbp1, hr141, stk1, hstk1, ?hmem⟩
  case grsp => exact hrsp1.trans (bhm_ret _)
  case hmem =>
    rw [show k + 147 + 1 = k + 148 from rfl] at Hm1
    first | ecancel | (simp only [Std.ExtHashMap.sep_emp] at Hm1; ecancel)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Return segment: directive 148 to the return (`retq`, directive 155). Memory unchanged. -/
theorem bh_enc_e (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k)
    (s : MachineData) (rsp ra rbp0 : UInt64) (dst v cap : BitVec 64) (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 8#64 - 152 })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
      ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 v.toInt).At (rsp.toBitVec - 104)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = { toBitVec := dst }
        ∧ st.data.regs.rbx = { toBitVec := v } ∧ st.data.regs.rcx = { toBitVec := cap }
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = rsp + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = s.regs.r14 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 v.toInt).At (rsp.toBitVec - 104)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 148)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst hrsp
  have hrl := rsp.toNat_lt_size
  simp only [UInt64.size] at hrl
  kat hk BhMarshal 148
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 dst.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 149
  apply load_step_at _ _ (rsp.toBitVec - 104) _ _ (Int.toBytes 8 v.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 150
  apply load_step_at _ _ (rsp.toBitVec - 96) _ _ (Int.toBytes 8 cap.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 151
  intro _
  kat hk BhMarshal 152
  intro _
  kat hk BhMarshal 153
  kat hk BhMarshal 154
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 155
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_mem⟩
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; eaddr)

end E2eScal.Bh
