import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.Code
import Prysm.AttestationData.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.SyncCommitteeMessage.Code
import Prysm.PendingConsolidation.Statements

/-!
# Independent hand STATEMENTS of the two accept theorems (hold-out; statements only, no proof)

Hand-written BEFORE the proof generator (`gen/scal/scalgen.py`) was run on
either type and before any generator output for them was read.
Sources: the Go receiver layout (IR `go_fields` in `prysm/ir/ir-mainnet.json`), the SSZ layout
(consensus-specs; `Prysm/SyncCommitteeMessage/SpecDescription.lean`, `Prysm/PendingConsolidation/SpecDescription.lean`), the frame facts of the two `.S` files
(`prysm/go1.26.10/link-set/norm`), and the statement shape of the earlier hand accept theorems
`Prysm.BeaconBlockHeader.Decode.accept` (callee fields and fresh 32-byte slices in a `0x60` frame) and
`Prysm.PendingPartialWithdrawal.Decode.accept_statement` (callee fields in a `0x48` frame). These abbrevs are the targets of the
`--same-as-prop` identity check and of the hand proofs. They are not generator output.

## `Decode.accept_statement` — `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ`

    func (s *SyncCommitteeMessage) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 144 { return ssz.ErrSize }
        if err = s.Slot.UnmarshalSSZ(buf[0:8]); err != nil { return fmt.Errorf("Slot: %w", err) }
        s.BlockRoot = append(make([]byte, 0, 32), buf[8:40]...)
        if err = s.ValidatorIndex.UnmarshalSSZ(buf[40:48]); err != nil { return fmt.Errorf(...) }
        s.Signature = append(make([]byte, 0, 96), buf[48:144]...)
        return err }

Receiver: protoc struct, IR `go_fields` (size 104): `state` 0, `Slot` 8, `BlockRoot` 16 (ptr, len, cap),
`ValidatorIndex` 40, `Signature` 48 (ptr, len, cap), `unknownFields` 72, `sizeCache` 96 (the last two in `R`).
Frame (`.S`): `sub $0x60` (as BeaconBlockHeader); spills `0x70(%rsp)` = entry rsp + 8 (rax), `0x78(%rsp)` = + 16
(rbx), `0x88(%rsp)` = + 32 (rdi); `0x28(%rsp)` / `0x30(%rsp)` = entry rsp − 64 / − 56 (the ValidatorIndex callee's
rax / rbx, nil on this path); `0x38(%rsp)` = entry rsp − 48 (slice pointer save); `0x0…0x17(%rsp)` = entry rsp − 104
(24 bytes; the callees spill rbx at − 96). Call return slot entry rsp − 112; below it `lo` (S + 8 bytes: the callees'
saved rbp at − 120 and the runtime callees' stack). Error-path slots `0x40…0x5f(%rsp)` are untouched (in `R`).
Two makeslice / memmove calls, 128 heap bytes; the last call (memmove of Signature) is directive 140, so the
return slot holds directive 141 at the end.

## `Prysm.PendingConsolidation.Decode.accept_statement` — `(*v1alpha1.PendingConsolidation).UnmarshalSSZ`

    func (p *PendingConsolidation) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 16 { return ssz.ErrSize }
        if err = p.SourceIndex.UnmarshalSSZ(buf[0:8]); err != nil { return fmt.Errorf("SourceIndex: %w", err) }
        if err = p.TargetIndex.UnmarshalSSZ(buf[8:16]); err != nil { return fmt.Errorf("TargetIndex: %w", err) }
        return err }

Receiver: protoc struct, IR `go_fields` (size 56): `state` 0, `SourceIndex` 8, `TargetIndex` 16,
`unknownFields` 24, `sizeCache` 48 (the last two in `R`).
Frame (`.S`): `sub $0x48` (as PendingPartialWithdrawal); spills `0x58(%rsp)` = entry rsp + 8 (rax), `0x60(%rsp)` = + 16
(rbx), `0x70(%rsp)` = + 32 (rdi). The callee (ValidatorIndex, twice; leaf function, function spec `Prysm.ValidatorIndex.Decode.accept_function_spec`) has its
return slot at entry rsp − 88, saves rbp at entry rsp − 96 (`lo`) and spills its rbx to entry rsp − 72 (`sp1`).
The callee checks the stack guard at entry rsp − 88, hence `guard + 88 < rsp`. The second call is directive 55,
so the return slot holds directive 56 at the end. Error-path frame slots are untouched on this path (in `R`).
After the split of this module, the declarations of the other types are in `Prysm/PendingConsolidation/Statements.lean`.
-/

open Machine Runtime Prysm.AttestationData.Code Prysm.SyncCommitteeMessage.Code
variable [Host]

namespace Prysm.SyncCommitteeMessage

/-- Hand statement of the accept path of `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ`: on a 144-byte input
it returns nil and the receiver holds Slot = buf[0:8], a fresh BlockRoot slice equal to buf[8:40] (len = cap = 32),
ValidatorIndex = buf[40:48] and a fresh Signature slice equal to buf[48:144] (len = cap = 96); input, `state`,
the spills, the caller's frame `R` and the stack guard are unchanged; 128 heap bytes are used. The two delegated
fields go through the callees' code (`Prysm.Slot.Code.unmarshalSSZ`, `Prysm.ValidatorIndex.Code.unmarshalSSZ` placed in the host). -/
abbrev Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (in0 rt in1 sig : List UInt8) (hin0 : in0.length = 8) (hrt : rt.length = 32) (hin1 : in1.length = 8)
    (hsig : sig.length = 96)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast a8 aP1 aL1 aC1 a40 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (hs28 : s28.length = 8) (hs30 : s30.length = 8) (hl38 : l38.length = 8)
    (hrs : rslot.length = 8) (hast : ast.length = 8) (ha8 : a8.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (ha40 : a40.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40)) ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (a40.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 48)) ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 144) (hav : 128 ≤ avail)
    (hms : MakesliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (spl lo' : List UInt8), spl.length = 24 ∧ lo'.length = S + 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 141)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 128)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (rt.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 40)) ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56)) ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (rt.At p1) ⋆ Eq (sig.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.SyncCommitteeMessage
