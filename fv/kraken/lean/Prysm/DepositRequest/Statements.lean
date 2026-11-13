import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.CheckpointAndEpoch
import Prysm.Checkpoint.Code
import Prysm.AttestationData.Code
import Prysm.BeaconBlockHeader.Code
import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BuilderDepositRequest.Code

/-!
# Independent hand STATEMENTS of four decoder accept paths and four encoder fast paths
(statements only, no proof)

Hand-written BEFORE the author opened the generated modules
`Gen5F24{Bbr,Dpr,Pdc,Vid}Dec.lean` and `Gen6F24{Bbr,Bpf,Pdc,Vid}Enc.lean` or their kind lines. These generated files
were committed unedited (one-shot runs); this session built and kind-checked them without printing them.
Sources: the Go receiver layout (IR `go_fields` of `prysm/ir/ir-mainnet.json`, gc amd64 offsets), the SSZ layout
(field sizes in IR order), the `.S` files of `prysm/go1.26.10/e2e/f24/link/norm/` (frame, guard, spills, stack slots
touched on the path and their contents at the return, the directive of the last call), the statement shape of the
committed hand statements `Prysm.Deposit_Data.Decode.accept_statement`, `Prysm.SyncAggregatorSelectionData.Decode.accept_statement`, `Prysm.PendingDeposit.Decode.accept_statement`,
`Prysm.SyncCommitteeMessage.Decode.accept_statement` (decoders), `Prysm.PendingPartialWithdrawal.Encode.fast_path_statement`, `Prysm.SyncCommitteeMessage.Encode.fast_path_statement`,
`Prysm.PowBlock.Encode.fast_path_statement` (encoders), and the interface text of `enc2/L/OUT.md` (chunk order: saved rbp, home slots ascending,
other slots by first touch, the return slot; existentials in creation order). Independence limit: the layout
rules come from that interface text and the earlier hand statements; the parameters are read from the `.S` by hand.

Choice (classes with no independently tied statement before this unit):
| type | side | class |
| --- | --- | --- |
| DepositRequest | decoder | frame `0x20`, no call, 48 + 32 + u64 + 96 + a trailing in-line u64 (Deposit_Data code + one field) |
| BeaconBlocksByRangeRequest | decoder | frame `0x38`, Slot call then two in-line u64 (three fields in that frame) |
| PartialDataColumnGroupID | decoder | frame `0x40`, bytes 32 then a Slot call (one slice + a trailing call) |
| ValidatorIdentity | decoder | frame `0x50`, call / bytes 48 / call (a new frame size and field mix) |
| BuilderPreferences | encoder | one overlay u64 (Gwei) via a 32-byte temp, frame `0x48`, no `rax` home spill |
| BeaconBlocksByRangeRequest | encoder | overlay temp + two register u64, frame `0x70`, small guard (PendingPartialWithdrawal shape, other guard) |
| PartialDataColumnGroupID | encoder | bytes 32 with `memmove`, then an overlay temp AFTER the call, frame `0x68` |
| ValidatorIdentity | encoder | overlay temp / bytes 48 with `memmove` / overlay temp, frame `0x90`, guard `0x18` |

## Decoders (frame facts; offsets from the entry rsp)

- DepositRequest: `.S` = the Deposit_Data decoder with `cmp $0xc0` and, before the epilogue,
  `mov 0x38(%rsp),%rcx; mov 0xb8(%rcx),%rcx; mov %rcx,0x58(%rdx)` (Index = buf[184:192] → Go 88). Frame `sub $0x20`;
  spills + 8 (rax), + 16 (rbx); slice save − 16; runtime area − 40 (24 bytes); return slot − 48; last runtime call
  (memmove of Signature) directive 106. Receiver (size 128): `state` 0, Pubkey 8, WithdrawalCredentials 32, Amount 56,
  Signature 64, Index 88.
- BeaconBlocksByRangeRequest: `.S` = the SyncAggregatorSelectionData decoder with `cmp $0x18` and one more in-line
  store `mov 0x10(%rcx),%rcx; mov %rcx,0x18(%rsi)` (Step). Frame `sub $0x38`; spills + 8, + 16; Slot call at
  directive 18 (return slot − 72, callee rbp − 80, callee rbx spill − 56). Receiver (size 64): `state` 0, StartSlot 8,
  Count 16, Step 24.
- PartialDataColumnGroupID: frame `sub $0x40`; spills + 8 (rax), + 16 (rbx), + 32 (rdi); slice save − 32 (`0x28(%rsp)`);
  area − 72 (24 bytes; the callee spills rbx at − 64); one makeslice / memmove (32 heap bytes); Slot call at
  directive 56 (return slot − 80, `lo` from − 88 − S); `guard + 80 < rsp`. Receiver (size 72): `state` 0,
  BeaconBlockRoot 8, Slot 32.
- ValidatorIdentity: frame `sub $0x50`; spills + 8, + 16, + 32; ValidatorIndex call (directive 18) first, then the
  48-byte slice (save `0x28(%rsp)` = − 48), then the Epoch call (directive 91, the last call); area − 88 (24 bytes;
  callee rbx spill − 80); return slot − 96; `lo` from − 104 − S; `guard + 96 < rsp`; 48 heap bytes. Error-path slots
  `0x30…0x4f(%rsp)` are in `R`. Receiver (size 80): `state` 0, Index 8, Pubkey 16, ActivationEpoch 40.

## Encoders (fast path: `len(dst) + SizeSSZ ≤ cap(dst)`, byte fields of exact length)

- BuilderPreferences: frame `0x48`, small guard; touched: saved rbp, + 16 (rbx), the zeroed 32-byte temp at − 40
  (`movups` at − 40 and − 24; Gwei value stored at − 40). No store to + 8 on the fast path. Receiver: `state` 0,
  MaxExecutionPayment 8.
- BeaconBlocksByRangeRequest: frame `0x70`, small guard; + 8, + 16; temp at − 40 / − 24 (StartSlot at − 40); Count and
  Step stored from a register.
- PartialDataColumnGroupID: frame `0x68`, small guard; + 8, + 16; − 24 (dst pointer), − 64 (capacity), − 72 (len + 32);
  memmove (directive 36; return slot − 120, scratch below); then the temp at − 56 / − 40 (Slot at − 56).
- ValidatorIdentity: frame `0x90`, guard `lea -0x18(%rsp)`; + 8, + 16; temp − 56 / − 40 (Index at − 56); − 24 (dst
  pointer), − 104 (len + 56), − 96 (capacity); memmove (directive 64; return slot − 160); temp − 88 / − 72
  (ActivationEpoch at − 88).
-/

open Machine Runtime TestTarget Prysm.Checkpoint.Code Prysm.AttestationData.Code Prysm.DepositRequest.Code
variable [Host]

open Codec
namespace Prysm.DepositRequest

/-- Hand statement of the accept path of `(*v1.DepositRequest).UnmarshalSSZ`: on a 192-byte input it returns nil
and the receiver holds fresh Pubkey (48) / WithdrawalCredentials (32) / Signature (96) slices equal to buf[0:48] /
buf[48:80] / buf[88:184] (len = cap), Amount = buf[80:88] and Index = buf[184:192]; input, `state`, the spills, the
caller's frame `R` and the stack guard are unchanged; 176 heap bytes are used. -/
abbrev Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (pk wc amt sig idx : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8)
    (hsig : sig.length = 96) (hidx : idx.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 aN aP3 aL3 aC3 aI : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8) (haN : aN.length = 8)
    (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8) (haI : aI.length = 8)
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
      ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80)) ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
      ⋆ Eq (idx.At (s.regs.rbx.toBitVec + 184))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aN.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64)) ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80)) ⋆ Eq (aI.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 192) (hav : 176 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 p3 : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 106)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 176)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec) ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80)) ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (idx.At (s.regs.rbx.toBitVec + 184))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72)) ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (idx.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (pk.At p1) ⋆ Eq (wc.At p2) ⋆ Eq (sig.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- Hand statement of the accept path of `(*v1alpha1.BeaconBlocksByRangeRequest).UnmarshalSSZ`: on a 24-byte input
it returns nil and the receiver holds StartSlot = buf[0:8] (through the callee `slotUnmarshalSSZ`), Count = buf[8:16] and
Step = buf[16:24]; input, `state`, the spills, the caller's frame `R` and the stack guard are unchanged. -/
abbrev _root_.Prysm.BeaconBlocksByRangeRequest.Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.BeaconBlocksByRangeRequest.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlocksByRangeRequest.Code.unmarshalSSZ k)
    (kS : Nat) (hkS : slotUnmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh slotUnmarshalSSZ kS)
    (in0 in1 in2 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8) (hin2 : in2.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 sp1 rslot lo ast a8 a16 a24 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hsp1 : sp1.length = 8) (hrs : rslot.length = 8) (hlo : lo.length = 8)
    (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8) (ha24 : a24.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (in2.At (s.regs.rbx.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (a24.At (s.regs.rax.toBitVec + 24)) ⋆ R)
    (hguard : guard.toNat + 72 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 24),
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
          ⋆ Eq (in2.At (s.regs.rbx.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (in2.At (s.regs.rax.toBitVec + 24)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- Hand statement of the accept path of `(*v1alpha1.PartialDataColumnGroupID).UnmarshalSSZ`: on a 40-byte input it
returns nil and the receiver holds a fresh BeaconBlockRoot slice equal to buf[0:32] (len = cap = 32) and Slot =
buf[32:40] (through the callee `slotUnmarshalSSZ`); input, `state`, the spills, the caller's frame `R` and the stack guard
are unchanged; 32 heap bytes are used. -/
abbrev _root_.Prysm.PartialDataColumnGroupID.Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.PartialDataColumnGroupID.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PartialDataColumnGroupID.Code.unmarshalSSZ k)
    (kS : Nat) (hkS : slotUnmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh slotUnmarshalSSZ kS)
    (rt sl : List UInt8) (hrt : rt.length = 32) (hsl : sl.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP1 aL1 aC1 aS : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (hl28 : l28.length = 8) (hrs : rslot.length = 8) (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haS : aS.length = 8)
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
      ⋆ Eq (rt.At s.regs.rbx.toBitVec) ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aS.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 40) (hav : 32 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 : BitVec 64) (spl lo' : List UInt8), spl.length = 24 ∧ lo'.length = S + 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (rt.At s.regs.rbx.toBitVec) ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (rt.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- Hand statement of the accept path of `(*v1alpha1.ValidatorIdentity).UnmarshalSSZ`: on a 64-byte input it returns
nil and the receiver holds Index = buf[0:8] (callee `Prysm.ValidatorIndex.Code.unmarshalSSZ`), a fresh Pubkey slice equal to buf[8:56]
(len = cap = 48) and ActivationEpoch = buf[56:64] (callee `Prysm.Epoch.Code.unmarshalSSZ`); input, `state`, the spills, the caller's
frame `R` and the stack guard are unchanged; 48 heap bytes are used. -/
abbrev _root_.Prysm.ValidatorIdentity.Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.ValidatorIdentity.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.ValidatorIdentity.Code.unmarshalSSZ k)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (in0 pk in1 : List UInt8) (hin0 : in0.length = 8) (hpk : pk.length = 48) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast a8 aP1 aL1 aC1 a40 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (hl28 : l28.length = 8) (hrs : rslot.length = 8) (hast : ast.length = 8) (ha8 : a8.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (ha40 : a40.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 104 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (pk.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 56))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (a40.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 64) (hav : 48 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 (S + 8)) (hmm : MemmoveC (S + 8)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 : BitVec 64) (spl lo' : List UInt8), spl.length = 24 ∧ lo'.length = S + 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 91)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 104 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 48)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (pk.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 56))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (pk.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- BuilderPreferences encoder fast path (`state`; MaxExecutionPayment `primitives.Gwei` at Go 8). Frame `0x48`,
small guard; stack: saved rbp, home slot `rsp + 16`, the zeroed temp at `rsp − 40` / `rsp − 24` (Gwei at − 40). -/
abbrev _root_.Prysm.BuilderPreferences.Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.BuilderPreferences.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BuilderPreferences.Code.marshalSSZTo k)
    (ast v0 pre d0 : List UInt8)
    (hast : ast.length = 8) (hv0 : v0.length = 8) (hd0 : d0.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 : List UInt8)
    (hfp : fp.length = 8) (hs2 : s2.length = 8) (ht40 : t40.length = 16) (ht24 : t24.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 88 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 8 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- BeaconBlocksByRangeRequest encoder fast path (`state`; StartSlot `primitives.Slot` at Go 8, Count `uint64` at 16,
Step `uint64` at 24). Frame `0x70`, small guard; stack: saved rbp, home slots `rsp + 8`, `rsp + 16`, the zeroed temp
at `rsp − 40` / `rsp − 24` (StartSlot at − 40). Count and Step are stored from a register. -/
abbrev _root_.Prysm.BeaconBlocksByRangeRequest.Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.BeaconBlocksByRangeRequest.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BeaconBlocksByRangeRequest.Code.marshalSSZTo k)
    (ast v0 v1 v2 pre d0 d1 d2 : List UInt8)
    (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hv2 : v2.length = 8)
    (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t40 t24 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8)
    (ht40 : t40.length = 16) (ht24 : t24.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (v2.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 128 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 24 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 24 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (v2.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- PartialDataColumnGroupID encoder fast path (`state`; BeaconBlockRoot `[]byte` 32 at Go 8, Slot `primitives.Slot`
at 32). Frame `0x68`, small guard; stack: saved rbp, home slots `rsp + 8`, `rsp + 16`; `rsp − 24` (pointer),
`rsp − 64` (capacity), `rsp − 72` (len + 32), the zeroed temp `rsp − 56` / `rsp − 40` (Slot at − 56, written after the
`memmove`), the `memmove` return slot `rsp − 120` and the scratch. -/
abbrev _root_.Prysm.PartialDataColumnGroupID.Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.PartialDataColumnGroupID.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PartialDataColumnGroupID.Code.marshalSSZTo k)
    (ast v1 c0 b0 pre d0 d1 : List UInt8)
    (hast : ast.length = 8) (hv1 : v1.length = 8) (hc0 : c0.length = 8) (hb0 : b0.length = 32)
    (hd0 : d0.length = 32) (hd1 : d1.length = 8)
    (p0 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l24 l64 l72 t56 t40 rslot : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl24 : l24.length = 8)
    (hl64 : l64.length = 8) (hl72 : l72.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (scr x1 x2 : List UInt8), scr.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 36)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- ValidatorIdentity encoder fast path (`state`; Index `primitives.ValidatorIndex` at Go 8, Pubkey `[]byte` 48 at
16, ActivationEpoch `primitives.Epoch` at 40). Frame `0x90`, guard `lea -0x18(%rsp)`; stack: saved rbp, home slots
`rsp + 8`, `rsp + 16`; the zeroed temp `rsp − 56` / `rsp − 40` (Index at − 56); `rsp − 24` (pointer), `rsp − 104`
(len + 56), `rsp − 96` (capacity); the zeroed temp `rsp − 88` / `rsp − 72` (ActivationEpoch at − 88, after the
`memmove`); the `memmove` return slot `rsp − 160` and the scratch. -/
abbrev _root_.Prysm.ValidatorIdentity.Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.ValidatorIdentity.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.ValidatorIdentity.Code.marshalSSZTo k)
    (ast v0 v2 c1 b1 pre d0 d1 d2 : List UInt8)
    (hast : ast.length = 8) (hv0 : v0.length = 8) (hv2 : v2.length = 8) (hc1 : c1.length = 8)
    (hb1 : b1.length = 48) (hd0 : d0.length = 8) (hd1 : d1.length = 48) (hd2 : d2.length = 8)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8)
    (ht56 : t56.length = 16) (ht40 : t40.length = 16) (hl24 : l24.length = 8) (hl104 : l104.length = 8)
    (hl96 : l96.length = 8) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (b1.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56)) ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 64 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 scr x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ scr.length = S
          ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 56).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 64)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.DepositRequest
