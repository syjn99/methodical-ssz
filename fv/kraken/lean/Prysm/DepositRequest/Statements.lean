import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.Code
import Prysm.AttestationData.Code
import Prysm.BeaconBlockHeader.Code
import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BuilderDepositRequest.Code
import Prysm.BeaconBlocksByRangeRequest.Statements
import Prysm.BuilderPreferences.Statements
import Prysm.PartialDataColumnGroupID.Statements
import Prysm.ValidatorIdentity.Statements

/-!
# Independent hand STATEMENTS of four decoder accept paths and four encoder fast paths
(statements only, no proof)

Hand-written BEFORE the author opened the generated modules
`Gen5F24{Bbr,Dpr,Pdc,Vid}Dec.lean` and `Gen6F24{Bbr,Bpf,Pdc,Vid}Enc.lean` or their kind lines. These generated files
were committed unedited (one-shot runs); this session built and kind-checked them without printing them.
Sources: the Go receiver layout (IR `go_fields` of `prysm/ir/ir-mainnet.json`, gc amd64 offsets), the SSZ layout
(field sizes in IR order), the `.S` files of `prysm/go1.26.10/link-set/norm/` (frame, guard, spills, stack slots
touched on the path and their contents at the return, the directive of the last call), the statement shape of the
committed hand statements `Prysm.Deposit_Data.Decode.accept_statement`, `Prysm.SyncAggregatorSelectionData.Decode.accept_statement`, `Prysm.PendingDeposit.Decode.accept_statement`,
`Prysm.SyncCommitteeMessage.Decode.accept_statement` (decoders), `Prysm.PendingPartialWithdrawal.Encode.fast_path_statement`, `Prysm.SyncCommitteeMessage.Encode.fast_path_statement`,
`Prysm.PowBlock.Encode.fast_path_statement` (encoders), and the interface rules of the encoder statements (chunk order: saved rbp, home slots ascending,
other slots by first touch, the return slot; existentials in creation order). Independence limit: the layout
rules come from that interface text and the earlier hand statements; the parameters are read from the `.S` by hand.

Choice (classes with no independently tied statement before this work):
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
After the split of this module, the declarations of the other types are in `Prysm/BeaconBlocksByRangeRequest/Statements.lean`, `Prysm/BuilderPreferences/Statements.lean`, `Prysm/PartialDataColumnGroupID/Statements.lean`, `Prysm/ValidatorIdentity/Statements.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code Prysm.AttestationData.Code Prysm.DepositRequest.Code
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
    (hms : MakesliceC Heap ElfData.PrysmTarget.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
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

end Prysm.DepositRequest
