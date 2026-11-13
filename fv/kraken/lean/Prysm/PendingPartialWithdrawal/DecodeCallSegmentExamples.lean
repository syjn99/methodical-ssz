import Codec.Kind.CalleeDecode
import Codec.FixedBytesDecodePadding
import Prysm.Deposit_Data.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.AttestationData.Code
import Prysm.Checkpoint.Code

/-!
# Hand-written example instances of the `p2dec --gen3` lemmas on the development sites

One theorem and one `_kind` line per lemma per site, in the shape a generated theorem is to have (the idiom
of `Gen2Examples.lean`). Examples for the generator unit; not generator output (the text was produced by a
scratch script from the `.S` files and the kind texts). Sites: the seven `uint64`-overlay callee fields of
the development decoders (PendingPartialWithdrawal `Index`, `WithdrawableEpoch`; BeaconBlockHeader `Slot`,
`ProposerIndex`; AttestationData `Slot`, `CommitteeIndex`; Checkpoint `Epoch`) with their argument set-ups,
the two-directive inline uint64 read (PendingPartialWithdrawal `Amount`) and the padded byte segment
(Deposit_Data `WithdrawalCredentials`). Parameters are read from the `.S` files (directive index = line − 1).
The callee specification stays a hypothesis `U64CalleeAcc "<callee label>"` of each call-block theorem.
-/

open Machine Runtime TestTarget
variable [Host]

open Codec
namespace Prysm.PendingPartialWithdrawal

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Index` (callee decoder field, Go offset 8): argument set-up, first-field form, directives 15–16. -/
theorem Decode.example_call_Index_arg (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (rcv aF : BitVec 64) (hF : rcv + (8 : Int64).toBitVec = aF)
    (s : MachineData) (hrax : s.regs.rax.toBitVec = rcv),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 15 + 2 + padLen false) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 15)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callArgFirst false 8) 15 hk
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, Codec.callArgFirst, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  with_reducible exact Codec.callarg_first_seg false _ (k + 15) hA
theorem Decode.example_call_Index_arg_kind : ∀ (h : Host), type_of% (@Decode.example_call_Index_arg h) = @Codec.callArgFirstKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ false 8 15 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Index`: call block of the callee decoder, directives 17–19, continuation label at 47. -/
theorem Decode.example_call_Index_call (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
    (sp dst src aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = dst) (hrbx : s.regs.rbx.toBitVec = src)
    (hrcx : s.regs.rcx = 8)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 17)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_b9") 17 hk
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_b9") 47 hk
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 47)
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg _ _ (k + 17) (k + 47) hA hB hl
theorem Decode.example_call_Index_call_kind : ∀ (h : Host), type_of% (@Decode.example_call_Index_call h) = @Codec.callDecSegKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_b9" 17 47 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `WithdrawableEpoch` (callee decoder field, SSZ offset 16, Go offset 24): argument set-up, `lea` form, first part, directives 48–53. -/
theorem Decode.example_call_WithdrawableEpoch_arg1 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aB aD aR aSrc aF : BitVec 64)
    (hB' : sp + (96 : Int64).toBitVec = aB) (hD : sp + (112 : Int64).toBitVec = aD) (hR : sp + (88 : Int64).toBitVec = aR)
    (hSrc : bf + (16 : Int64).toBitVec = aSrc) (hF : rcv + (24 : Int64).toBitVec = aF)
    (vD : List UInt8) (hvD : vD.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 48 + 6) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rbx.toBitVec = bf ∧ st.data.regs.rdx.toBitVec = aSrc
        ∧ st.data.regs.rax.toBitVec = rcv ∧ st.data.regs.rsi.toBitVec = aF
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 48)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callArgLea 96 16 112 (-16) 88 24) 48 hk
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, Codec.callArgLea, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  with_reducible exact Codec.callarg_lea_seg _ _ _ _ _ _ (k + 48) hA
theorem Decode.example_call_WithdrawableEpoch_arg1_kind : ∀ (h : Host), type_of% (@Decode.example_call_WithdrawableEpoch_arg1 h) = @Codec.callArgLeaKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ 96 16 112 (-16) 88 24 48 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Amount` (inline uint64, two-directive form, SSZ offset 8, Go offset 16): decode segment, directives 54–55, scratch register r8. -/
theorem Decode.example_call_Amount_seg (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (bf rcv aSrc aF : BitVec 64) (hSrc : bf + (8 : Int64).toBitVec = aSrc) (hF : rcv + (16 : Int64).toBitVec = aF)
    (v vF : List UInt8) (hv : v.length = 8) (hvF : vF.length = 8)
    (R : DataMem → Prop)
    (s : MachineData) (hrbx : s.regs.rbx.toBitVec = bf) (hrax : s.regs.rax.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq (v.At aSrc) ⋆ Eq (vF.At aF) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 54 + 2) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx
        ∧ (∀ r : Reg64, r ≠ Reg64.r8 → st.data.regs.get64 r = s.regs.get64 r)
        ∧ (Eq (v.At aSrc) ⋆ Eq (v.At aF) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 54)⟩ := by
  have hA := Codec.infix_sub (q := Codec.u64DecRR Reg64.r8 8 16) 54 hk
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, Codec.u64DecRR, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hX : Codec.U64RRReg Reg64.r8 := by decide
  with_reducible exact Codec.u64dec_rr_seg Reg64.r8 hX _ _ (k + 54) hA
theorem Decode.example_call_Amount_seg_kind : ∀ (h : Host), type_of% (@Decode.example_call_Amount_seg h) = @Codec.u64DecRRSegKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ Reg64.r8 8 16 54 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `WithdrawableEpoch`: argument set-up, `lea` form, second part, directives 56–58. -/
theorem Decode.example_call_WithdrawableEpoch_arg2 (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀
    (s : MachineData),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 56 + 3) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rsi ∧ st.data.regs.rbx = s.regs.rdx ∧ st.data.regs.rcx = 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 56)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callArgMov) 56 hk
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, Codec.callArgMov, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  with_reducible exact Codec.callarg_mov_seg (k + 56) hA
theorem Decode.example_call_WithdrawableEpoch_arg2_kind : ∀ (h : Host), type_of% (@Decode.example_call_WithdrawableEpoch_arg2 h) = @Codec.callArgMovKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ 56 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `WithdrawableEpoch`: call block of the callee decoder, directives 59–61, continuation label at 88. -/
theorem Decode.example_call_WithdrawableEpoch_call (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ")
    (sp dst src aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = dst) (hrbx : s.regs.rbx.toBitVec = src)
    (hrcx : s.regs.rcx = 8)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 88 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 59 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 59)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159") 59 hk
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159") 88 hk
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 88)
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg _ _ (k + 59) (k + 88) hA hB hl
theorem Decode.example_call_WithdrawableEpoch_call_kind : ∀ (h : Host), type_of% (@Decode.example_call_WithdrawableEpoch_call h) = @Codec.callDecSegKind h Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159" 59 88 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Slot` (callee decoder field, Go offset 8): argument set-up, first-field form, directives 15–16. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_call_Slot_arg (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀
    (rcv aF : BitVec 64) (hF : rcv + (8 : Int64).toBitVec = aF)
    (s : MachineData) (hrax : s.regs.rax.toBitVec = rcv),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 15 + 2 + padLen false) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 15)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callArgFirst false 8) 15 hk
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, Codec.callArgFirst, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  with_reducible exact Codec.callarg_first_seg false _ (k + 15) hA
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_call_Slot_arg_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_call_Slot_arg h) = @Codec.callArgFirstKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ false 8 15 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Slot`: call block of the callee decoder, directives 17–19, continuation label at 46. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_call_Slot_call (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ")
    (sp dst src aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = dst) (hrbx : s.regs.rbx.toBitVec = src)
    (hrcx : s.regs.rcx = 8)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 46 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 17)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b9") 17 hk
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b9") 46 hk
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 46)
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg _ _ (k + 17) (k + 46) hA hB hl
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_call_Slot_call_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_call_Slot_call h) = @Codec.callDecSegKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b9" 17 46 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ProposerIndex` (callee decoder field, SSZ offset 8, Go offset 16): argument set-up by reload, directives 47–54 (padding `nop`). -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_call_ProposerIndex_arg (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aB aD aR aSrc aF : BitVec 64)
    (hB' : sp + (120 : Int64).toBitVec = aB) (hD : sp + (136 : Int64).toBitVec = aD) (hR : sp + (112 : Int64).toBitVec = aR)
    (hSrc : bf + (8 : Int64).toBitVec = aSrc) (hF : rcv + (16 : Int64).toBitVec = aF)
    (vD : List UInt8) (hvD : vD.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47 + 7 + padLen true) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rbx.toBitVec = aSrc ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 47)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callArgReload true 120 8 136 (-8) 112 16) 47 hk
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, Codec.callArgReload, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  with_reducible exact Codec.callarg_reload_seg true _ _ _ _ _ _ (k + 47) hA
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_call_ProposerIndex_arg_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_call_ProposerIndex_arg h) = @Codec.callArgReloadKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ true 120 8 136 (-8) 112 16 47 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `ProposerIndex`: call block of the callee decoder, directives 55–57, continuation label at 85. -/
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_call_ProposerIndex_call (k : Nat) (hk : Prysm.BeaconBlockHeader.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlockHeader.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ")
    (sp dst src aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = dst) (hrbx : s.regs.rbx.toBitVec = src)
    (hrcx : s.regs.rcx = 8)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 85 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 55 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 55)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154") 55 hk
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154") 85 hk
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 85)
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.BeaconBlockHeader.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg _ _ (k + 55) (k + 85) hA hB hl
theorem _root_.Prysm.BeaconBlockHeader.Decode.example_call_ProposerIndex_call_kind : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Decode.example_call_ProposerIndex_call h) = @Codec.callDecSegKind h Prysm.BeaconBlockHeader.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154" 55 85 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Slot` (callee decoder field, Go offset 8): argument set-up, first-field form, directives 15–16. -/
theorem _root_.Prysm.AttestationData.Decode.example_call_Slot_arg (k : Nat) (hk : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ k) :
    ∀
    (rcv aF : BitVec 64) (hF : rcv + (8 : Int64).toBitVec = aF)
    (s : MachineData) (hrax : s.regs.rax.toBitVec = rcv),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 15 + 2 + padLen false) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 15)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callArgFirst false 8) 15 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callArgFirst, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  with_reducible exact Codec.callarg_first_seg false _ (k + 15) hA
theorem _root_.Prysm.AttestationData.Decode.example_call_Slot_arg_kind : ∀ (h : Host), type_of% (@Prysm.AttestationData.Decode.example_call_Slot_arg h) = @Codec.callArgFirstKind h Prysm.AttestationData.Code.unmarshalSSZ false 8 15 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Slot`: call block of the callee decoder, directives 17–19, continuation label at 47. -/
theorem _root_.Prysm.AttestationData.Decode.example_call_Slot_call (k : Nat) (hk : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ")
    (sp dst src aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = dst) (hrbx : s.regs.rbx.toBitVec = src)
    (hrcx : s.regs.rcx = 8)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 17)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_c7") 17 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_c7") 47 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 47)
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg _ _ (k + 17) (k + 47) hA hB hl
theorem _root_.Prysm.AttestationData.Decode.example_call_Slot_call_kind : ∀ (h : Host), type_of% (@Prysm.AttestationData.Decode.example_call_Slot_call h) = @Codec.callDecSegKind h Prysm.AttestationData.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_c7" 17 47 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `CommitteeIndex` (callee decoder field, SSZ offset 8, Go offset 16): argument set-up by reload, directives 48–54. -/
theorem _root_.Prysm.AttestationData.Decode.example_call_CommitteeIndex_arg (k : Nat) (hk : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aB aD aR aSrc aF : BitVec 64)
    (hB' : sp + (136 : Int64).toBitVec = aB) (hD : sp + (152 : Int64).toBitVec = aD) (hR : sp + (128 : Int64).toBitVec = aR)
    (hSrc : bf + (8 : Int64).toBitVec = aSrc) (hF : rcv + (16 : Int64).toBitVec = aF)
    (vD : List UInt8) (hvD : vD.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 48 + 7 + padLen false) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rbx.toBitVec = aSrc ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 48)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callArgReload false 136 8 152 (-8) 128 16) 48 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callArgReload, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  with_reducible exact Codec.callarg_reload_seg false _ _ _ _ _ _ (k + 48) hA
theorem _root_.Prysm.AttestationData.Decode.example_call_CommitteeIndex_arg_kind : ∀ (h : Host), type_of% (@Prysm.AttestationData.Decode.example_call_CommitteeIndex_arg h) = @Codec.callArgReloadKind h Prysm.AttestationData.Code.unmarshalSSZ false 136 8 152 (-8) 128 16 48 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `CommitteeIndex`: call block of the callee decoder, directives 55–57, continuation label at 85. -/
theorem _root_.Prysm.AttestationData.Decode.example_call_CommitteeIndex_call (k : Nat) (hk : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ")
    (sp dst src aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = dst) (hrbx : s.regs.rbx.toBitVec = src)
    (hrcx : s.regs.rcx = 8)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 85 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 55 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 55)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_167") 55 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_167") 85 hk
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 85)
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.AttestationData.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg _ _ (k + 55) (k + 85) hA hB hl
theorem _root_.Prysm.AttestationData.Decode.example_call_CommitteeIndex_call_kind : ∀ (h : Host), type_of% (@Prysm.AttestationData.Decode.example_call_CommitteeIndex_call h) = @Codec.callDecSegKind h Prysm.AttestationData.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_167" 55 85 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Epoch` (callee decoder field, Go offset 8): argument set-up, first-field form, directives 14–16 (padding `nop`). -/
theorem _root_.Prysm.Checkpoint.Decode.example_call_Epoch_arg (k : Nat) (hk : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ k) :
    ∀
    (rcv aF : BitVec 64) (hF : rcv + (8 : Int64).toBitVec = aF)
    (s : MachineData) (hrax : s.regs.rax.toBitVec = rcv),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 14 + 2 + padLen true) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 14)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callArgFirst true 8) 14 hk
    (by simp only [Prysm.Checkpoint.Code.unmarshalSSZ, Codec.callArgFirst, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  with_reducible exact Codec.callarg_first_seg true _ (k + 14) hA
theorem _root_.Prysm.Checkpoint.Decode.example_call_Epoch_arg_kind : ∀ (h : Host), type_of% (@Prysm.Checkpoint.Decode.example_call_Epoch_arg h) = @Codec.callArgFirstKind h Prysm.Checkpoint.Code.unmarshalSSZ true 8 14 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Epoch`: call block of the callee decoder, directives 17–19, continuation label at 47. -/
theorem _root_.Prysm.Checkpoint.Decode.example_call_Epoch_call (k : Nat) (hk : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ")
    (sp dst src aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = dst) (hrbx : s.regs.rbx.toBitVec = src)
    (hrcx : s.regs.rcx = 8)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 47 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 17)⟩ := by
  have hA := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4") 17 hk
    (by simp only [Prysm.Checkpoint.Code.unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4") 47 hk
    (by simp only [Prysm.Checkpoint.Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 47)
    (by simp only [Prysm.Checkpoint.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.Checkpoint.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.calldec_seg _ _ (k + 17) (k + 47) hA hB hl
theorem _root_.Prysm.Checkpoint.Decode.example_call_Epoch_call_kind : ∀ (h : Host), type_of% (@Prysm.Checkpoint.Decode.example_call_Epoch_call h) = @Codec.callDecSegKind h Prysm.Checkpoint.Code.unmarshalSSZ "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4" 17 47 := by
  intro h; with_reducible rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `WithdrawalCredentials` (32 bytes, SSZ offset 48, Go offset 32): decode segment with the padding `nop` before `callq runtime.makeslice`, directives 47–72. -/
theorem _root_.Prysm.Deposit_Data.Decode.example_call_WithdrawalCredentials_seg (k : Nat) (hk : Prysm.Deposit_Data.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.Deposit_Data.Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + (48 : Int64).toBitVec = aR) (hB' : sp + (56 : Int64).toBitVec = aB) (hS : sp + (24 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (32 : Int64).toBitVec = aP) (hL : rcv + (40 : Int64).toBitVec = aL) (hC : rcv + (48 : Int64).toBitVec = aC)
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
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
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
  have hA := Codec.infix_sub (q := Codec.bytesDecHeadP true 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113" 48 40 48) 47 hk
    (by simp only [Prysm.Deposit_Data.Code.unmarshalSSZ, Codec.bytesDecHeadP, Codec.bytesDecHeadPad, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.bytesDecMid 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_154" 48 56 24 32 40 48 48) 61 hk
    (by simp only [Prysm.Deposit_Data.Code.unmarshalSSZ, Codec.bytesDecMid, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 61)
    (by simp only [Prysm.Deposit_Data.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.Deposit_Data.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.bytesdec_seg_p true 32 (Or.inl rfl) _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) hA hB hl
theorem _root_.Prysm.Deposit_Data.Decode.example_call_WithdrawalCredentials_seg_kind : ∀ (h : Host), type_of% (@Prysm.Deposit_Data.Decode.example_call_WithdrawalCredentials_seg h) = @Codec.bytesDecSegKind h 32 Prysm.Deposit_Data.Code.unmarshalSSZ 47 61 48 56 24 32 40 48 48 := by
  intro h; with_reducible rfl

end Prysm.PendingPartialWithdrawal
