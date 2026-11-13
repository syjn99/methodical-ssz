import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BlobIdentifier.EncoderCode
import Prysm.Deposit_Data.EncodeFastPathStatements
import Prysm.PendingPartialWithdrawal.EncodeFastPathStatements
import Prysm.SyncCommitteeMessage.EncodeFastPathStatements

/-!
# Independent hand statements of four encoder fast paths

Written by hand BEFORE the generated `Gen6{Pb,Sc,Pw,Dd}Enc.lean` fast-path theorems or their kind lines were
opened. Sources: the Go layout in `prysm/ir/ir-mainnet.json` (`go_fields`, gc amd64 offsets), the SSZ layout
of the four containers, the `.S` files of `prysm/go1.26.10/link-set/norm/` (frame, guard, stack slots
touched on the fast path and their contents at the return) and the shape of the committed hand statements
`Prysm.BeaconBlockHeader.Encode.fast_path` / `Prysm.Eth1Data.Encode.fast_path` (binder order and memory order per the
interface rules of the encoder statements: saved rbp, home slots ascending, other slots by first touch,
the return slot; existentials in creation order).

**Encoder fast path only**: `len(dst) + SizeSSZ ≤ cap(dst)` and every byte-vector field of its exact length.
No growslice branch, no length reject, no morestack path. Not a complete encoder result.

| type | class | frame | guard | memmove |
| --- | --- | --- | --- | --- |
| PowBlock | frame test (`moveSliceNoCapNoScan` test not taken), no `state` word, 3 × bytes 32 | `0x50` | small | yes |
| SyncCommitteeMessage | overlay uint64 (Slot, ValidatorIndex) via stack temps, bytes 32 + 96 | `0xa8` | `0x30` | yes |
| PendingPartialWithdrawal | three uint64 (two overlay) via stack temps, no call | `0x90` | `0x18` | no |
| Deposit_Data | bytes 48 + 32 + uint64 + bytes 96 | `0x88` | `0x10` | yes |

Each statement is an `abbrev … : Prop`; `Prysm/PowBlock/GeneratedEncodeFastPathSameAsHand.lean` proves `type_of% generated = this` by `rfl`.
After the split of this module, the declarations of the other types are in `Prysm/Deposit_Data/EncodeFastPathStatements.lean`, `Prysm/PendingPartialWithdrawal/EncodeFastPathStatements.lean`, `Prysm/SyncCommitteeMessage/EncodeFastPathStatements.lean`.
-/

open Machine Runtime Codec Prysm.PowBlock.Code
variable [Host]

namespace Prysm.PowBlock

/-- PowBlock (`BlockHash`, `ParentHash`, `TotalDifficulty`: `[]byte` of size 32 at Go 0, 24, 48; no `state`
word). Frame `0x50`; stack: saved rbp, home slots `rsp + 8` (receiver), `rsp + 16` (dst pointer), temps
`rsp − 16` (pointer), `rsp − 32` (length / capacity), `rsp − 40` (capacity / length), the `memmove` return
slot `rsp − 96` and the scratch below it. The epilogue's frame test (`ptr − rsp < 0x60` → copy) is not taken. -/
abbrev Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (c0 c1 c2 b0 b1 b2 pre d0 d1 d2 : List UInt8)
    (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8)
    (hb0 : b0.length = 32) (hb1 : b1.length = 32) (hb2 : b2.length = 32)
    (hd0 : d0.length = 32) (hd1 : d1.length = 32) (hd2 : d2.length = 32)
    (p0 p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l32 l40 rslot : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8)
    (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq (b0.At p0) ⋆ Eq (b1.At p1) ⋆ Eq (b2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 64)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 96 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 96 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 96 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (scr : List UInt8), scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 96).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 94)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (b0.At p0) ⋆ Eq (b1.At p1) ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 64)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.PowBlock
