import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.Code
import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BuilderDepositRequest.Code
import Prysm.BLSToExecutionChange.Statements
import Prysm.ValidatorRegistrationV1.Statements
import Prysm.WithdrawalRequest.Statements

/-!
# Independent hand STATEMENTS of two decoder accept paths and two encoder fast paths with a
20-byte vector field (statements only, no proof)

Hand-written BEFORE the generators were changed for the 20-byte kind, so before any
generated theorem of these four functions existed (the one-shot runs on the 24 flat types refused all four: "new field kind (b20)").
Sources: the Go receiver layout (IR `go_fields` of `prysm/ir/ir-mainnet.json`, gc amd64 offsets), the SSZ layout
(field sizes in IR order), the `.S` files of `prysm/go1.26.10/link-set/norm/` (frame, guard, spills, stack slots
touched on the path and their contents at the return, the directive of the last call), the statement shape of the
committed hand statements `Prysm.DepositRequest.Decode.accept_statement` (decoders, frame `0x20`, no callee) and
`Prysm.Deposit_Data.Encode.fast_path_statement`, `Prysm.ValidatorIdentity.Encode.fast_path_statement` (encoders), and the interface rules of the encoder statements (chunk order: saved
rbp, home slots ascending, other slots by first touch, the return slot; existentials in creation order).
Independence limit: the layout rules come from that interface text and the earlier hand statements; the parameters
are read from the `.S` by hand. Development data, no hold-out.

| type | side | class |
| --- | --- | --- |
| BuilderExitRequest | decoder | frame `0x20`, no call, bytes 20 (offset-0 form) then bytes 48 |
| WithdrawalRequest | decoder | frame `0x20`, no call, bytes 20, bytes 48, a trailing in-line u64 at SSZ offset 68 |
| BLSToExecutionChange | encoder | overlay temp, bytes 48 (`jae` capacity form), bytes 20 (`jb` capacity form), frame `0x70` |
| ValidatorRegistrationV1 | encoder | bytes 20 first, two register u64, bytes 48; frame `0x88`, guard `lea -0x10(%rsp)` |

## Decoders (frame facts; offsets from the entry rsp)

- BuilderExitRequest: frame `sub $0x20`; `cmp $0x44,%rcx` (68 bytes); spills + 8 (rax), + 16 (rbx); slice save
  `0x18(%rsp)` = − 16; runtime area − 40 (24 bytes); return slot − 48; the last runtime call (memmove of Pubkey) is
  directive 66, so the return slot holds the address of directive 67. Receiver (size 56): `state` 0,
  SourceAddress 8 / 16 / 24, Pubkey 32 / 40 / 48. Input: SourceAddress buf[0:20], Pubkey buf[20:68]. Ends with
  `xor %eax,%eax; xor %ebx,%ebx`.
- WithdrawalRequest: as BuilderExitRequest with `cmp $0x4c` (76 bytes) and, before the epilogue,
  `mov 0x38(%rsp),%rcx; mov 0x44(%rcx),%rcx; mov %rcx,0x38(%rdx)` (Amount = buf[68:76] → Go 56). Last runtime call
  directive 66. Receiver (size 64): `state` 0, SourceAddress 8, ValidatorPubkey 32, Amount 56.

## Encoders (fast path: `len(dst) + SizeSSZ ≤ cap(dst)`, byte fields of exact length)

- BLSToExecutionChange: frame `0x70` (rsp − 120 after the prologue), small guard; home slots + 16 (rbx), + 8 (rax);
  zeroed temp `0x30(%rsp)` = − 72 / − 56 (ValidatorIndex at − 72); then `0x58` = − 32 (capacity, then len + 76),
  `0x50` = − 40 (len + 56, then capacity), `0x68` = − 16 (pointer); memmove return slot − 128 (last memmove
  directive 91, return address directive 92). Receiver: `state` 0, ValidatorIndex 8, FromBlsPubkey 16 / 24 / 32,
  ToExecutionAddress 40 / 48 / 56. Output: buf[0:8], buf[8:56], buf[56:76].
- ValidatorRegistrationV1: frame `0x88` (rsp − 144), guard `lea -0x10(%rsp)`; home slots + 16, + 8; `0x78` = − 24
  (pointer), `0x58` = − 56 (len + 20), `0x60` = − 48 (capacity); memmove return slot − 152; then `0x70` = − 32
  (len + 84), `0x68` = − 40 (capacity), `0x80` = − 16 (pointer); last memmove directive 92 (return address 93).
  GasLimit and Timestamp are stored from a register. Receiver: `state` 0, FeeRecipient 8 / 16 / 24, GasLimit 32,
  Timestamp 40, Pubkey 48 / 56 / 64. Output: buf[0:20], buf[20:28], buf[28:36], buf[36:84].
After the split of this module, the declarations of the other types are in `Prysm/BLSToExecutionChange/Statements.lean`, `Prysm/ValidatorRegistrationV1/Statements.lean`, `Prysm/WithdrawalRequest/Statements.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code Prysm.BuilderExitRequest.Code
variable [Host]

open Codec
namespace Prysm.BuilderExitRequest

/-- Hand statement of the accept path of `(*v1.BuilderExitRequest).UnmarshalSSZ`: on a 68-byte input it returns nil
and the receiver holds fresh SourceAddress (20) / Pubkey (48) slices equal to buf[0:20] / buf[20:68] (len = cap);
input, `state`, the spills, the caller's frame `R` and the stack guard are unchanged; 68 heap bytes are used. -/
abbrev Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k)
    (sa pk : List UInt8) (hsa : sa.length = 20) (hpk : pk.length = 48)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
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
      ⋆ Eq (sa.At s.regs.rbx.toBitVec) ⋆ Eq (pk.At (s.regs.rbx.toBitVec + 20))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 68) (hav : 68 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S),
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
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 67)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 68)
          ⋆ Eq (sa.At s.regs.rbx.toBitVec) ⋆ Eq (pk.At (s.regs.rbx.toBitVec + 20))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 40)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (sa.At p1) ⋆ Eq (pk.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.BuilderExitRequest
