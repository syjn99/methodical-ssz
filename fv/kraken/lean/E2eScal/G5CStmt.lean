import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.CheckpointAndEpoch
import Prysm.Checkpoint.Code
import Prysm.AttestationData.Code
import E2eScal.BhCode
import E2eScal.H6Code

/-!
# Independent hand STATEMENTS of three `p2dec --gen5` accept theorems (statements only, no proof)

Hand-written BEFORE the author opened the generated modules `Gen5SaDec.lean`,
`Gen5VbDec.lean`, `Gen5VeDec.lean` or their kind lines. These generated files were already committed.
This session did not read them, did not print their statements, and did not read the worked example `Gen5ExVe.lean`.
Sources: the Go receiver layout (IR `go_fields` in `prysm/ir/ir-mainnet.json`), the SSZ layout (two 8-byte fields),
the frame facts of the three `.S` files (`prysm/go1.26.10/e2e/h6/link/norm`, opened in an earlier hold-out), the first directives of
the callee `.S` files, and the statement shape of the earlier hand statement `E2eScal.H5.pc_accept_stmt`
(two callee fields, frame `0x48`). The identity with the generated accept theorem is checked in a later commit.
A review asked for SyncAggregatorSelectionData and ValidatorBalance (frame `0x38`, no hand statement of that
frame class). The brief also names VoluntaryExit. Its frame class (`0x48`) is already tied by hand statements.

## `sa_accept_stmt` — `(*v1alpha1.SyncAggregatorSelectionData).UnmarshalSSZ`

    func (s *SyncAggregatorSelectionData) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 16 { return ssz.ErrSize }
        if err = s.Slot.UnmarshalSSZ(buf[0:8]); err != nil { return fmt.Errorf("Slot: %w", err) }
        s.SubcommitteeIndex = ssz.UnmarshallUint64(buf[8:16])
        return err }

(Go text read back from the `.S`.)
Receiver: protoc struct, IR `go_fields` (size 56): `state` 0, `Slot` 8, `SubcommitteeIndex` 16, `unknownFields` 24,
`sizeCache` 48 (the last two in `R`).
Frame (`.S`): `sub $0x38`, so rsp = entry rsp − 64 in the body. Spills `0x48(%rsp)` = entry rsp + 8 (rax) and
`0x50(%rsp)` = + 16 (rbx; stored twice, directives 7 and 12). No rdi spill. One callee call (Slot, directive 17);
its return slot is entry rsp − 72, so the return slot holds directive 18 at the end. The callee (`push %rbp`,
`sub $0x48`, `mov %rbx,0x60(%rsp)`) saves rbp at entry rsp − 80 (`lo`) and spills its rbx to entry rsp − 56
(`sp1`); it checks the stack guard at entry rsp − 72, hence `guard + 72 < rsp`. After the call (`je` to `_b4`):
`mov 0x50(%rsp),%rcx; mov 0x8(%rcx),%rcx; mov 0x48(%rsp),%rdx; mov %rcx,0x10(%rdx)`, then the epilogue
`add $0x38; pop %rbp; retq`. rax = rbx = 0 from the callee. Error-path slots `0x28…0x37(%rsp)` are untouched (in `R`).

## `vb_accept_stmt` — `(*v1alpha1.ValidatorBalance).UnmarshalSSZ`

Same code shape as SyncAggregatorSelectionData with the callee ValidatorIndex: `Index` (Go offset 8) through
`ViUnmarshal`, `Balance` (Go offset 16) inline `uint64`. Receiver size 56 with the same tail words.

## `ve_accept_stmt` — `(*v1alpha1.VoluntaryExit).UnmarshalSSZ`

    func (v *VoluntaryExit) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 16 { return ssz.ErrSize }
        if err = v.Epoch.UnmarshalSSZ(buf[0:8]); err != nil { return fmt.Errorf("Epoch: %w", err) }
        if err = v.ValidatorIndex.UnmarshalSSZ(buf[8:16]); err != nil { return fmt.Errorf(...) }
        return err }

Receiver: IR `go_fields` (size 56): `state` 0, `Epoch` 8, `ValidatorIndex` 16, then `unknownFields`, `sizeCache` (in `R`).
Frame (`.S`): `sub $0x48` (as PendingConsolidation); spills `0x58(%rsp)` = + 8 (rax), `0x60(%rsp)` = + 16 (rbx),
`0x70(%rsp)` = + 32 (rdi). Callees Epoch (directive 17) then ValidatorIndex (directive 55); return slot entry
rsp − 88, so it holds directive 56 at the end; callee rbp at − 96 (`lo`), callee rbx spill at − 72 (`sp1`);
`guard + 88 < rsp`.
-/

open Machine Runtime TestTarget Prysm.Checkpoint.Code Prysm.AttestationData.Code E2eScal.H6Code E2eScal.BhCode
variable [Host]

namespace E2eScal.G5C

/-- Hand statement of the accept path of `(*v1alpha1.SyncAggregatorSelectionData).UnmarshalSSZ`: on a 16-byte
input it returns nil and the receiver holds Slot = buf[0:8] (through the callee `slotUnmarshalSSZ`) and
SubcommitteeIndex = buf[8:16]; input, `state`, the spills, the caller's frame `R` and the stack guard are
unchanged. -/
abbrev sa_accept_stmt : Prop :=
  ∀ (k : Nat) (hk : SaUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SaUnmarshal k)
    (kS : Nat) (hkS : slotUnmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh slotUnmarshalSSZ kS)
    (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 sp1 rslot lo ast a8 a16 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hsp1 : sp1.length = 8) (hrs : rslot.length = 8) (hlo : lo.length = 8)
    (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat + 72 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 16),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (sp1' lo' : List UInt8), sp1'.length = 8 ∧ lo'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (sp1'.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 18)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- Hand statement of the accept path of `(*v1alpha1.ValidatorBalance).UnmarshalSSZ`: on a 16-byte input it
returns nil and the receiver holds Index = buf[0:8] (through the callee `ViUnmarshal`) and Balance = buf[8:16];
input, `state`, the spills, the caller's frame `R` and the stack guard are unchanged. -/
abbrev vb_accept_stmt : Prop :=
  ∀ (k : Nat) (hk : VbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh VbUnmarshal k)
    (kV : Nat) (hkV : ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh ViUnmarshal kV)
    (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 sp1 rslot lo ast a8 a16 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hsp1 : sp1.length = 8) (hrs : rslot.length = 8) (hlo : lo.length = 8)
    (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat + 72 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 16),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (sp1' lo' : List UInt8), sp1'.length = 8 ∧ lo'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (sp1'.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 18)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- Hand statement of the accept path of `(*v1alpha1.VoluntaryExit).UnmarshalSSZ`: on a 16-byte input it returns
nil and the receiver holds Epoch = buf[0:8] and ValidatorIndex = buf[8:16] (through the callees `Prysm.Epoch.Code.unmarshalSSZ`,
`ViUnmarshal`); input, `state`, the spills, the caller's frame `R` and the stack guard are unchanged. -/
abbrev ve_accept_stmt : Prop :=
  ∀ (k : Nat) (hk : VeUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh VeUnmarshal k)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (kV : Nat) (hkV : ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh ViUnmarshal kV)
    (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lo ast a8 a16 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp1 : sp1.length = 8) (hrs : rslot.length = 8) (hlo : lo.length = 8)
    (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 16),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (sp1' lo' : List UInt8), sp1'.length = 8 ∧ lo'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (sp1'.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end E2eScal.G5C
