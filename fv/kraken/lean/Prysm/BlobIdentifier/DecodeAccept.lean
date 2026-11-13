import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Prysm.Eth1Data.DecodeAccept
import Prysm.BlobIdentifier.GeneratedDecodeRootFieldSegments

/-!
# Real Prysm `(*v1alpha1.BlobIdentifier).UnmarshalSSZ`, accept path, Go 1.26.10 machine code (hold-out)

Hand-written after the frozen generator ran on this hold-out type. The BlockRoot segment is the raw
generator theorem `Prysm.BlobIdentifier.Decode.generated_root_BlockRoot_seg` (`Prysm/BlobIdentifier/GeneratedDecodeRootFieldSegments.lean`, unedited). The head and the
composition are the text of `Prysm/Eth1Data/DecodeAccept.lean` with the BlobIdentifier indices and without the second root
segment; `eth1_data_addr` and `Prysm.Eth1Data.Decode.stack_low_eq` are reused from `Prysm/Eth1Data/DecodeAccept.lean`.

    func (b *BlobIdentifier) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 40 { return ssz.ErrSize }
        b.BlockRoot = append(make([]byte, 0, 32), buf[0:32]...)
        b.Index = ssz.UnmarshallUint64(buf[32:40])
        return err }

Receiver (protoc struct, gc amd64 layout from `prysm/ir/ir-mainnet.json` `go_fields`): `state` 0,
`BlockRoot` 8 (ptr, len, cap), `Index` 32; `unknownFields` 40 and `sizeCache` 64 are not touched on this
path (in `R`). The code agrees: the receiver stores are at 8, 16, 24 and 32.

Directive indices of `Prysm.BlobIdentifier.Code.unmarshalSSZ` (index = line − 1 of the `.S`): 2–3 stack guard,
4–7 prologue, 8 `nop`, 9–10 `cmp $0x28,%rcx; jne L_e2`, 11–12 spills; 13–36 the BlockRoot segment
(generated); 37–38 + `L_c7` 45–46 pointer reload and store; 47–49 Index (`buf[32:40]` to receiver + 32);
epilogue 50–54. Stack as in `Prysm/Eth1Data/DecodeAccept.lean`.
-/

open Machine Runtime Codec Prysm.BlobIdentifier.Code
variable [Host]

namespace Prysm.BlobIdentifier

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
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 40) :
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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.BlobIdentifier).UnmarshalSSZ` (Go 1.26.10)**: on a 40-byte input it
returns nil and the receiver holds a fresh 32-byte BlockRoot = buf[0:32] (len = cap = 32) and
Index = buf[32:40]; the input, `state`, the caller's frame `R` and the stack guard are unchanged;
32 heap bytes are used. -/
theorem Decode.accept (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (r1 idx : List UInt8) (hr1 : r1.length = 32) (hidx : idx.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aN : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN : aN.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (r1.At s.regs.rbx.toBitVec) ⋆ Eq (idx.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aN.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 40) (hav : 32 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 32)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (r1.At s.regs.rbx.toBitVec) ⋆ Eq (idx.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (idx.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (r1.At p1)
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
  -- BlockRoot: the generated segment theorem (raw generator output, `Prysm/BlobIdentifier/GeneratedDecodeRootFieldSegments.lean`), 13 → 37
  refine eventually_trans _ _ _ _ (Prysm.BlobIdentifier.Decode.generated_root_BlockRoot_seg k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 8) (rax.toBitVec + 16) (rax.toBitVec + 24) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Prysm.Eth1Data.Decode.stack_low_eq _ _)
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
  -- directives 37–38, L_c7 (45), 46; Index 47–49 (hand: no template for an inline uint64 read)
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
  apply load_step_at _ _ (rbx.toBitVec + 32) _ _ idx _ _ (by eth1_data_addr) (by ecancel) (by exact hidx)
  unfold_step
  step_directive hk unmarshalSSZ 49
  apply store_step_at _ _ (rax.toBitVec + 32) _ _ _ aN _ _ (by rw [hrdx2]; try eth1_data_addr) (by ecancel)
    (by exact haN)
  intro m4' H4
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl idx hidx] at H4
  unfold_step
  -- epilogue 50–54
  step_directive hk unmarshalSSZ 50
  intro _
  step_directive hk unmarshalSSZ 51
  intro _
  step_directive hk unmarshalSSZ 52
  step_directive hk unmarshalSSZ 53
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 54
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by eth1_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  rw [show k + 26 + 5 + 1 = k + 32 from rfl] at H4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, p1, spl1, lo1, hspl1, hlo1, ?_⟩
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

end Prysm.BlobIdentifier
