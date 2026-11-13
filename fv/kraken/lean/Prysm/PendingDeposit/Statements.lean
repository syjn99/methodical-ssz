import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.CheckpointAndEpoch
import Prysm.Checkpoint.Code
import Prysm.AttestationData.Code
import Prysm.PendingDeposit.Code
import Prysm.PowBlock.Statements

/-!
# Independent hand STATEMENTS of the two accept theorems (hold-out; statements only, no proof)

Hand-written BEFORE the proof generator (`gen/scal/scalgen.py`) was run on
either type and before any generator output for them was read.
Sources: the Go receiver layout (IR `go_fields` in `prysm/ir/ir-mainnet.json`), the SSZ layout
(consensus-specs; `Prysm/PendingDeposit/SpecDescription.lean`, `Prysm/PowBlock/SpecDescription.lean`), the frame facts of the two `.S` files
(`prysm/go1.26.10/e2e/h6/link/norm`), and the statement shape of the earlier hand accept theorems
`Prysm.SyncCommitteeMessage.Decode.accept_statement` (fresh byte slices and a callee field) and `Prysm.Deposit_Data.Decode.accept_statement` (fresh byte
slices in a `0x20` frame). These abbrevs are the targets of the hand proofs. They are not generator output.
`--gen4 --compose` refuses, so no identity check runs against them.

## `Decode.accept_statement` — `(*v1alpha1.PendingDeposit).UnmarshalSSZ`

    func (p *PendingDeposit) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 192 { return ssz.ErrSize }
        p.PublicKey = append(make([]byte, 0, 48), buf[0:48]...)
        p.WithdrawalCredentials = append(make([]byte, 0, 32), buf[48:80]...)
        p.Amount = ssz.UnmarshallUint64(buf[80:88])
        p.Signature = append(make([]byte, 0, 96), buf[88:184]...)
        if err = p.Slot.UnmarshalSSZ(buf[184:192]); err != nil { return fmt.Errorf("Slot: %w", err) }
        return err }

(Go text read back from the `.S`; the generated Go source was not opened.)
Receiver: protoc struct, IR `go_fields` (size 128): `state` 0, `PublicKey` 8 (ptr, len, cap), `WithdrawalCredentials`
32, `Amount` 56, `Signature` 64, `Slot` 88, `unknownFields` 96, `sizeCache` 120 (the last two in `R`).
Frame (`.S`): `sub $0x40`; spills `0x50(%rsp)` = entry rsp + 8 (rax), `0x58(%rsp)` = + 16 (rbx), `0x68(%rsp)` = + 32
(rdi); `0x28(%rsp)` = entry rsp − 32 (slice pointer save `l28`); `0x0…0x17(%rsp)` = entry rsp − 72 (24 bytes; the
Slot callee spills rbx at − 64). Call return slot entry rsp − 80; below it `lo` (S + 8 bytes: the callee's saved
rbp at − 88 and the runtime callees' stack). The callee checks the stack guard at entry rsp − 80, hence
`guard + 80 < rsp`. Frame slots `0x18…0x27(%rsp)` and the error-path slots `0x30…0x3f(%rsp)` are untouched on
this path (in `R`). Three makeslice / memmove calls, 176 heap bytes; the last call (Slot) is directive 130, so
the return slot holds directive 131 at the end.

## `Prysm.PowBlock.Decode.accept_statement` — `(*v1alpha1.PowBlock).UnmarshalSSZ`

    func (p *PowBlock) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 96 { return ssz.ErrSize }
        p.BlockHash = append(make([]byte, 0, 32), buf[0:32]...)
        p.ParentHash = append(make([]byte, 0, 32), buf[32:64]...)
        p.TotalDifficulty = append(make([]byte, 0, 32), buf[64:96]...)
        return err }

(Go text read back from the `.S`.)
Receiver: native Go struct (`beacon_state_types.go`), IR `go_fields` (size 72): `BlockHash` 0 (ptr, len, cap),
`ParentHash` 24, `TotalDifficulty` 48. No `state` word.
Frame (`.S`): `sub $0x20` (as Deposit_Data); spills `0x30(%rsp)` = entry rsp + 8 (rax), `0x38(%rsp)` = + 16 (rbx);
`0x18(%rsp)` = entry rsp − 16 (slice pointer save `l18`); `0x0…0x17(%rsp)` = entry rsp − 40 (24 bytes, `spl`);
runtime call return slot entry rsp − 48; `lo` = the `S` bytes below it. Three makeslice / memmove calls,
96 heap bytes; the last runtime call (memmove of TotalDifficulty) is directive 103, so its return address is
directive 104. The epilogue sets rax = rbx = 0 (`xor`).
After the split of this module, the declarations of the other types are in `Prysm/PowBlock/Statements.lean`.
-/

open Machine Runtime Prysm.AttestationData.Code Prysm.PendingDeposit.Code
variable [Host]

namespace Prysm.PendingDeposit

/-- Hand statement of the accept path of `(*v1alpha1.PendingDeposit).UnmarshalSSZ`: on a 192-byte input it
returns nil and the receiver holds fresh PublicKey (48) / WithdrawalCredentials (32) / Signature (96) slices
equal to buf[0:48] / buf[48:80] / buf[88:184] (len = cap), Amount = buf[80:88] and Slot = buf[184:192]; input,
`state`, the spills, the caller's frame `R` and the stack guard are unchanged; 176 heap bytes are used. The
delegated field goes through the callee's code (`Prysm.Slot.Code.unmarshalSSZ` placed in the host). -/
abbrev Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (pk wc amt sig sl : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8)
    (hsig : sig.length = 96) (hsl : sl.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 aN aP3 aL3 aC3 aS : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (hl28 : l28.length = 8) (hrs : rslot.length = 8) (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8) (haN : aN.length = 8)
    (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8) (haS : aS.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (pk.At s.regs.rbx.toBitVec) ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80)) ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
      ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aN.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64)) ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80)) ⋆ Eq (aS.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 192) (hav : 176 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 p3 : BitVec 64) (spl lo' : List UInt8), spl.length = 24 ∧ lo'.length = S + 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 131)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 176)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec) ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80)) ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72)) ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1) ⋆ Eq (wc.At p2) ⋆ Eq (sig.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.PendingDeposit
