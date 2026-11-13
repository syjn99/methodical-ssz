import Codec.Kind.FixedBytesDecode
import Codec.Kind.InlineUint64
import Prysm.Eth1Data.Code
import Prysm.BlobIdentifier.Code
import Prysm.BlobIdentifier.DecodeFieldSegmentExamples
import Prysm.Eth1Data.DecodeFieldSegmentExamples

/-!
# Hand-written example instances of the `decoder --field-segments` lemmas on the development sites

One theorem and one `_kind` line per site, in the shape a generated theorem is to have (the text of
`Prysm/Eth1Data/GeneratedDecodeRootFieldSegments.lean` with the new lemma, template and kind names). Hand-written examples for the generator;
not generator output. Sites: `DepositMessage.PublicKey` (48 bytes, offset-0 form), the 32-byte sites of
the three development decoders re-derived with the size-parametric lemmas, and the three inline uint64
sites (`BlobIdentifier.Index`, `DepositMessage.Amount`, `Eth1Data.DepositCount`). Parameters are read from
the `.S` files (directive index = line − 1) and `prysm/ir/ir-mainnet.json`.
After the split of this module, the declarations of the other types are in `Prysm/BlobIdentifier/DecodeFieldSegmentExamples.lean`, `Prysm/Eth1Data/DecodeFieldSegmentExamples.lean`.
-/

open Machine Runtime Prysm.DepositMessage.Code
variable [Host]

open Codec
namespace Prysm.DepositMessage

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `PublicKey` (48 bytes, SSZ offset 0, Go offset 0): decode segment, directives 13–36. -/
theorem Decode.example_field_PublicKey_seg (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k) :
    ∀ (sp rcv bf aR aB aS aRet aLo aP aL aC : BitVec 64) (St : Nat)
    (hR : sp + (48 : Int64).toBitVec = aR) (hB' : sp + (56 : Int64).toBitVec = aB)
    (hS : sp + (24 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (0 : Int64).toBitVec = aP) (hL : rcv + (8 : Int64).toBitVec = aL)
    (hC : rcv + (16 : Int64).toBitVec = aC)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 48)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 48 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At bf)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 St) (hmm : MemmoveContract St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 26 + 11) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 26 + 5 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 48)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 48).At aL)
          ⋆ Eq ((Int.toBytes 8 48).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At bf)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 13)⟩ := by
  have hA := Codec.infix_sub (q := Codec.bytesDecHead 48 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_74" 48 8 16) 13 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.bytesDecMidOffsetZero 48 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_74" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_b0" 48 56 24 0 8 16) 26 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecMidOffsetZero, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 26)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.bytesdec_seg_offset_zero 48 (Or.inr (Or.inl rfl)) _ _ _ _ _ _ _ _ (k + 13) (k + 26) hA hB hl
theorem Decode.example_field_PublicKey_seg_kind : ∀ (h : Host), type_of% (@Decode.example_field_PublicKey_seg h) = @Codec.bytesDecSegOffsetZeroKind h 48 unmarshalSSZ 13 26 48 56 24 0 8 16 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `WithdrawalCredentials` (32 bytes, SSZ offset 48, Go offset 24): decode segment, directives 47–72. -/
theorem Decode.example_field_WithdrawalCredentials_seg (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k) :
    ∀ (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + (48 : Int64).toBitVec = aR) (hB' : sp + (56 : Int64).toBitVec = aB)
    (hS : sp + (24 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (24 : Int64).toBitVec = aP) (hL : rcv + (32 : Int64).toBitVec = aL)
    (hC : rcv + (40 : Int64).toBitVec = aC)
    (hSrc : bf + (48 : Int64).toBitVec = aSrc)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 32)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 St) (hmm : MemmoveContract St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 61 + 12) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 61 + 6 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 47)⟩ := by
  have hA := Codec.infix_sub (q := Codec.bytesDecHead 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_10c" 48 32 40) 47 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.bytesDecMid 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_10c" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_14d" 48 56 24 24 32 40 48) 61 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecMid, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 61)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.bytesdec_seg 32 (Or.inl rfl) _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) hA hB hl
theorem Decode.example_field_WithdrawalCredentials_seg_kind : ∀ (h : Host), type_of% (@Decode.example_field_WithdrawalCredentials_seg h) = @Codec.bytesDecSegKind h 32 unmarshalSSZ 47 61 48 56 24 24 32 40 48 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Amount` (inline uint64, SSZ offset 80, Go offset 48): decode segment, directives 83–85, scratch register rcx. -/
theorem Decode.example_field_Amount_seg (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k) :
    ∀ (sp rcv bf aB aSrc aF : BitVec 64)
    (hB' : sp + (56 : Int64).toBitVec = aB) (hSrc : bf + (80 : Int64).toBitVec = aSrc)
    (hF : rcv + (48 : Int64).toBitVec = aF)
    (rbp0 r140 : UInt64) (v vF : List UInt8) (hv : v.length = 8) (hvF : vF.length = 8)
    (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrdx : s.regs.rdx.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (v.At aSrc) ⋆ Eq (vF.At aF) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 83 + 3) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (v.At aSrc) ⋆ Eq (v.At aF) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 83)⟩ := by
  have hA := Codec.infix_sub (q := Codec.u64DecInline Reg64.rcx 56 80 48) 83 hk
    (by simp only [unmarshalSSZ, Codec.u64DecInline, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hX : Codec.U64InlineReg Reg64.rcx := by decide
  with_reducible exact Codec.u64dec_inline_seg Reg64.rcx hX _ _ _ (k + 83) hA
theorem Decode.example_field_Amount_seg_kind : ∀ (h : Host), type_of% (@Decode.example_field_Amount_seg h) = @Codec.u64DecInlineSegKind h unmarshalSSZ 83 56 80 48 := by
  intro h; with_reducible rfl

end Prysm.DepositMessage
