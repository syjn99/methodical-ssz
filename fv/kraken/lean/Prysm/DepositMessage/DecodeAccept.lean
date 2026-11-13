import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Prysm.Eth1Data.DecodeAccept
import Prysm.DepositMessage.GeneratedDecodeRootFieldSegments
import Prysm.DepositMessage.DecodeFieldSegmentOffsetZero

/-!
# Real Prysm `(*v1alpha1.DepositMessage).UnmarshalSSZ`, accept path, Go 1.26.10 machine code (hold-out)

Hand-written after the hold-out was opened. The WithdrawalCredentials segment is the
raw generator theorem `Prysm.DepositMessage.Decode.generated_root_WithdrawalCredentials_seg` (`Prysm/DepositMessage/GeneratedDecodeRootFieldSegments.lean`, unedited). The
PublicKey segment (48 bytes, source offset 0) is the hand lemma `Prysm.DepositMessage.bytes48dec_seg_z` (`Prysm/DepositMessage/DecodeFieldSegmentOffsetZero.lean`):
the generator does not read 48-byte fields. Amount (inline uint64) is by hand. The head and the composition
are the text of `Prysm/Eth1Data/DecodeAccept.lean`; `eth1_data_addr` and `Prysm.Eth1Data.Decode.stack_low_eq` are reused from it.

    func (d *DepositMessage) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 88 { return ssz.ErrSize }
        d.PublicKey = append(make([]byte, 0, 48), buf[0:48]...)
        d.WithdrawalCredentials = append(make([]byte, 0, 32), buf[48:80]...)
        d.Amount = ssz.UnmarshallUint64(buf[80:88])
        return err }

Receiver (native Go struct `beacon_state_types.go`, not protoc; gc amd64 layout from
`prysm/ir/ir-mainnet.json` `go_fields`, size 56): `PublicKey` 0 (ptr, len, cap), `WithdrawalCredentials` 24
(ptr, len, cap), `Amount` 48. The code agrees: the receiver stores are at 0, 8, 16, 24, 32, 40 and 48.

Directive indices of `Prysm.DepositMessage.Code.unmarshalSSZ` (index = line − 1 of the `.S`): 2–3 stack guard,
4–7 prologue, 8 `nop`, 9–10 `cmp $0x58,%rcx; jne L_17d`, 11–12 spills; 13–36 the PublicKey segment (hand);
37–38 + `L_c4` 45–46 pointer reload (`%rdi`) and store; 47–72 the WithdrawalCredentials segment (generated);
73–74 + `L_162` 81–82 pointer reload and store; 83–85 Amount (`buf[80:88]` to receiver + 48); epilogue 86–90.
Stack as in `Prysm/Eth1Data/DecodeAccept.lean`.
-/

open Machine Runtime Codec Prysm.DepositMessage.Code
variable [Host]

namespace Prysm.DepositMessage

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
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 88) :
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
  kat hk unmarshalSSZ 0
  kat hk unmarshalSSZ 1
  kat hk unmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk unmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk unmarshalSSZ 5
  kat hk unmarshalSSZ 6
  kat hk unmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk unmarshalSSZ 8
  kat hk unmarshalSSZ 9
  kat hk unmarshalSSZ 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk unmarshalSSZ 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk unmarshalSSZ 12
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  apply Eventually.done
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, ?_⟩
  rotate_right
  · ecancel
  all_goals (apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]; try rfl)
  all_goals eth1_data_addr

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.DepositMessage).UnmarshalSSZ` (Go 1.26.10)**: on an 88-byte input
it returns nil and the receiver holds a fresh 48-byte PublicKey = buf[0:48] (len = cap = 48), a fresh
32-byte WithdrawalCredentials = buf[48:80] (len = cap = 32) and Amount = buf[80:88]; the input, the caller's
frame `R` and the stack guard are unchanged; 80 heap bytes are used. -/
theorem Decode.accept (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (pk wc amt : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo aP1 aL1 aC1 aP2 aL2 aC2 aN : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8) (haN : aN.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (pk.At s.regs.rbx.toBitVec) ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
      ⋆ Eq (aP1.At s.regs.rax.toBitVec) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aN.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 88) (hav : 80 ≤ avail)
    (hms : MakesliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveC S) :
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
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 68)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 80)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec) ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (pk.At p1) ⋆ Eq (wc.At p2)
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
  -- PublicKey (hand: 48-byte offset-0 segment, `Prysm/DepositMessage/DecodeFieldSegmentOffsetZero.lean`), 13 → 37
  have hA1 := Codec.infix_sub (q := Prysm.DepositMessage.bytesDecHead48 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_74" 48 8 16) 13 hk
    (by simp only [unmarshalSSZ, Prysm.DepositMessage.bytesDecHead48, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB1 := Codec.infix_sub (q := Prysm.DepositMessage.bytesDecMidZ48 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_74" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_b0" 48 56 24 0 8 16) 26 hk
    (by simp only [unmarshalSSZ, Prysm.DepositMessage.bytesDecMidZ48, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl1 := Machine.label_at' hk hf (j := 26)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  refine eventually_trans _ _ _ _ (Prysm.DepositMessage.bytes48dec_seg_z _ _ _ _ _ _ _ _ (k + 13) (k + 26) hA1 hB1 hl1
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) rax.toBitVec (rax.toBitVec + 8) (rax.toBitVec + 16) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Prysm.Eth1Data.Decode.stack_low_eq _ _)
    (by simp) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 pk hpk spl rslot lo l18 aP1 aL1 aC1 hspl hrs hlo hl18 haP1 haL1 haC1
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
  -- directives 37–38, L_c4 (45), 46
  kat hk unmarshalSSZ 37
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 p1.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 38
  klabel hk hf unmarshalSSZ 45
  kat hk unmarshalSSZ 45
  kat hk unmarshalSSZ 46
  apply store_step_at _ _ rax.toBitVec _ _ _ (Int.toBytes 8 p1.toInt) _ _ (by rw [hrdx2]; try eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  -- WithdrawalCredentials: the generated segment theorem (raw scalgen output, `Prysm/DepositMessage/GeneratedDecodeRootFieldSegments.lean`), 47 → 73
  refine eventually_trans _ _ _ _ (Prysm.DepositMessage.Decode.generated_root_WithdrawalCredentials_seg k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 24) (rax.toBitVec + 32) (rax.toBitVec + 40)
    (rbx.toBitVec + 48) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Prysm.Eth1Data.Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    _ _ wc hwc spl1 (Int.toBytes 8 (Host.addrOf (k + 26 + 5 + 1)).toBitVec.toInt) lo1 (Int.toBytes 8 p1.toInt)
    aP2 aL2 aC2 hspl1 (Int.toBytes_length 8 _) hlo1 (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 48) (by omega) _ rfl rfl rfl (by ecancel) hms hmm) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, p2, spl2, lo2, hspl2, hlo2, hrdx3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hrsp3 hrbp3 hr143
  -- directives 73–74, L_162 (81), 82; Amount 83–85 (hand: no template for an inline uint64 read)
  kat hk unmarshalSSZ 73
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 p2.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 74
  klabel hk hf unmarshalSSZ 81
  kat hk unmarshalSSZ 81
  kat hk unmarshalSSZ 82
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ (Int.toBytes 8 p2.toInt) _ _ (by rw [hrdx3]; try eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk unmarshalSSZ 83
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 84
  apply load_step_at _ _ (rbx.toBitVec + 80) _ _ amt _ _ (by eth1_data_addr) (by ecancel) (by exact hamt)
  kunfold
  kat hk unmarshalSSZ 85
  apply store_step_at _ _ (rax.toBitVec + 48) _ _ _ aN _ _ (by rw [hrdx3]; try eth1_data_addr) (by ecancel)
    (by exact haN)
  intro m5' H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl amt hamt] at H5
  kunfold
  -- epilogue 86–90
  kat hk unmarshalSSZ 86
  intro _
  kat hk unmarshalSSZ 87
  intro _
  kat hk unmarshalSSZ 88
  kat hk unmarshalSSZ 89
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 90
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  rw [show k + 61 + 6 + 1 = k + 68 from rfl] at H5
  rw [show avail - 48 - 32 = avail - 80 by omega] at H5
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

end Prysm.DepositMessage
