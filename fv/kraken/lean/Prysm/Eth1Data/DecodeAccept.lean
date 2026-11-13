import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Prysm.Eth1Data.DecodeFieldSegmentOffsetZero

/-!
# Real Prysm `(*v1alpha1.Eth1Data).UnmarshalSSZ`, accept path, Go 1.26.10 machine code (hold-out)

Hand-written after the frozen generator ran on this hold-out type (not generator output: the one generator run,
emitted nothing). The head is the text of `Prysm/BeaconBlockHeader/DecodeHead.lean` without the callees; the composition
is the text of `Prysm/BeaconBlockHeader/DecodeAccept.lean` with the Eth1Data indices, offsets and two segments.

    func (e *Eth1Data) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 72 { return ssz.ErrSize }
        e.DepositRoot = append(make([]byte, 0, 32), buf[0:32]...)
        e.DepositCount = ssz.UnmarshallUint64(buf[32:40])
        e.BlockHash = append(make([]byte, 0, 32), buf[40:72]...)
        return err }

Receiver (protoc struct, gc amd64 layout from `prysm/ir/ir-mainnet.json` and the code): `state` 0,
`DepositRoot` 8 (ptr, len, cap), `DepositCount` 32, `BlockHash` 40 (ptr, len, cap); `unknownFields` and
`sizeCache` are not touched on this path (in `R`).

Directive indices of `Prysm.Eth1Data.Code.unmarshalSSZ` (index = line − 1 of the `.S`): 2–3 stack guard,
4–7 prologue (`push %rbp`, `sub $0x20`, rbx spill at rsp + 16), 8 `nop`, 9–10 `cmp $0x48,%rcx; jne L_17f`,
11–12 spills of rax, rbx at rsp + 8, + 16; 13–36 the DepositRoot segment (`rootdec_seg_source_offset_zero`, hand, source
offset 0); 37–38 + `L_c7` 45–46 pointer reload and store; 47–49 DepositCount (`buf[32:40]` to receiver + 32);
50–74 the BlockHash segment (frozen `rootdec_seg`, hand instance, source offset 40); 75–76 + `L_171` 84–85;
epilogue 86–90.

Stack (rsp = s.regs.rsp at entry): return slot; saved rbp at rsp − 8; argument spills rsp + 8 (receiver),
rsp + 16 (buf.ptr); frame rsp − 40 … rsp − 9: argument area rsp − 40 … rsp − 17 (`spl`), the pointer save
rsp − 16 (`l18`); the runtime callees' return slot rsp − 48 and their `S` stack bytes below it (`lo`).
-/

open Machine Runtime Codec Prysm.Eth1Data.Code
variable [Host]

namespace Prysm.Eth1Data

/-- Address equation by `toNat` and `omega` (as `beacon_block_header_addr`). -/
macro "eth1_data_addr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: from the entry through the length check and the spills 11–12 to directive 13. -/
theorem Decode.head (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (s : MachineData) (ra guard : UInt64) (fp s1 s2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 72) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 13) ∧ st.data.regs.rsp = s.regs.rsp - 40
        ∧ st.data.regs.rbp = s.regs.rsp - 8 ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  step_directive hk unmarshalSSZ 0
  step_directive hk unmarshalSSZ 1
  step_directive hk unmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk unmarshalSSZ 5
  step_directive hk unmarshalSSZ 6
  step_directive hk unmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk unmarshalSSZ 8
  step_directive hk unmarshalSSZ 9
  step_directive hk unmarshalSSZ 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk unmarshalSSZ 12
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  unfold_step
  apply Eventually.done
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, ?_⟩
  rotate_right
  · ecancel
  all_goals (apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]; try rfl)
  all_goals eth1_data_addr

theorem Decode.stack_low_eq (x : BitVec 64) (S : Nat) : x - 40 - 8 - BitVec.ofNat 64 S = x - 48 - BitVec.ofNat 64 S := by
  bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.Eth1Data).UnmarshalSSZ` (Go 1.26.10)**: on a 72-byte input it
returns nil and the receiver holds fresh 32-byte DepositRoot = buf[0:32] and BlockHash = buf[40:72]
(len = cap = 32 each) and DepositCount = buf[32:40]; the input, `state`, the caller's frame `R` and the
stack guard are unchanged; 64 heap bytes are used. -/
theorem Decode.accept (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (r1 cnt r2 : List UInt8) (hr1 : r1.length = 32) (hcnt : cnt.length = 8) (hr2 : r2.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aN aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN : aN.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (r1.At s.regs.rbx.toBitVec) ⋆ Eq (cnt.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (r2.At (s.regs.rbx.toBitVec + 40))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aN.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 72) (hav : 64 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 70)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 64)
          ⋆ Eq (r1.At s.regs.rbx.toBitVec) ⋆ Eq (cnt.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (r2.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (cnt.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (r1.At p1) ⋆ Eq (r2.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hrsp_lt : rsp.toNat < 2 ^ 64 := rsp.toNat_lt_size
  -- head: entry → directive 13
  refine eventually_trans _ _ _ _ (Decode.head k hk _ ra guard fp s1 s2 hfp h1 h2 _ (by dsimp only; ecancel)
    hguard hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- DepositRoot (hand, source offset 0), 13 → 37
  have hA1 := Codec.infix_sub (q := Codec.rootDecHead "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75" 48 16 24) 13 hk
    (by simp only [unmarshalSSZ, Codec.rootDecHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB1 := Codec.infix_sub (q := rootDecMidSourceOffsetZero "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_b2" 48 56 24 8 16 24) 26 hk
    (by simp only [unmarshalSSZ, rootDecMidSourceOffsetZero, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl1 := Machine.label_at' hk hf (j := 26)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  refine eventually_trans _ _ _ _ (rootdec_seg_source_offset_zero _ _ _ _ _ _ _ _ (k + 13) (k + 26) hA1 hB1 hl1
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 8) (rax.toBitVec + 16) (rax.toBitVec + 24) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 r1 hr1 spl rslot lo l18 aP1 aL1 aC1 hspl hrs hlo hl18 haP1 haL1 haC1
    _ Heap avail (by omega) d1
    (by rw [hrsp1]; first | rfl | (apply UInt64.toBitVec_inj.mp; simp))
    (by rw [hrbp1]) hr141
    (by ecancel) hms hmm) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, p1, spl1, lo1, hspl1, hlo1, hrdx2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrdx2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hrbp2 hr142 hrdx2 Hm2
  subst hrsp2 hrbp2 hr142
  -- instance directives 37–38, L_c7 (45), 46; DepositCount 47–49
  step_directive hk unmarshalSSZ 37
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 p1.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 38
  label_address hk hf unmarshalSSZ 45
  step_directive hk unmarshalSSZ 45
  step_directive hk unmarshalSSZ 46
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ (Int.toBytes 8 p1.toInt) _ _ (by rw [hrdx2]; try eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk unmarshalSSZ 47
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 48
  apply load_step_at _ _ (rbx.toBitVec + 32) _ _ cnt _ _ (by eth1_data_addr) (by ecancel) (by exact hcnt)
  unfold_step
  step_directive hk unmarshalSSZ 49
  apply store_step_at _ _ (rax.toBitVec + 32) _ _ _ aN _ _ (by rw [hrdx2]; try eth1_data_addr) (by ecancel)
    (by exact haN)
  intro m4' H4
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl cnt hcnt] at H4
  unfold_step
  -- BlockHash (frozen rootdec_seg, hand instance), 50 → 75
  have hA2 := Codec.infix_sub (q := Codec.rootDecHead "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_119" 48 48 56) 50 hk
    (by simp only [unmarshalSSZ, Codec.rootDecHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB2 := Codec.infix_sub (q := Codec.rootDecMid "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_119" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_15a" 48 56 24 40 48 56 40) 63 hk
    (by simp only [unmarshalSSZ, Codec.rootDecMid, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl2 := Machine.label_at' hk hf (j := 63)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  refine eventually_trans _ _ _ _ (Codec.rootdec_seg _ _ _ _ _ _ _ _ _ (k + 50) (k + 63) hA2 hB2 hl2
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 40) (rax.toBitVec + 48) (rax.toBitVec + 56)
    (rbx.toBitVec + 40) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    _ _ r2 hr2 spl1 (Int.toBytes 8 (Host.addrOf (k + 26 + 5 + 1)).toBitVec.toInt) lo1 (Int.toBytes 8 p1.toInt)
    aP2 aL2 aC2 hspl1 (Int.toBytes_length 8 _) hlo1 (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 32) (by omega) _ rfl rfl rfl (by ecancel) hms hmm) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, p2, spl2, lo2, hspl2, hlo2, hrdx3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hrsp3 hrbp3 hr143
  -- instance directives 75–76, L_171 (84), 85, epilogue 86–90
  step_directive hk unmarshalSSZ 75
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 p2.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 76
  label_address hk hf unmarshalSSZ 84
  step_directive hk unmarshalSSZ 84
  step_directive hk unmarshalSSZ 85
  apply store_step_at _ _ (rax.toBitVec + 40) _ _ _ (Int.toBytes 8 p2.toInt) _ _ (by rw [hrdx3]; try eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  unfold_step
  step_directive hk unmarshalSSZ 86
  intro _
  step_directive hk unmarshalSSZ 87
  intro _
  step_directive hk unmarshalSSZ 88
  step_directive hk unmarshalSSZ 89
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 90
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  rw [show k + 63 + 6 + 1 = k + 70 from rfl] at H5
  rw [show avail - 32 - 32 = avail - 64 by omega] at H5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, p1, p2, spl2, lo2, hspl2, hlo2, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; eth1_data_addr)
    | (apply UInt64.toBitVec_inj.mp; simp [BitVec.xor_self])

end Prysm.Eth1Data
