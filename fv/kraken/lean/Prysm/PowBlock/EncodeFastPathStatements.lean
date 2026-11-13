import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BlobIdentifier.EncoderCode

/-!
# Independent hand statements of four encoder fast paths

Written by hand BEFORE the generated `Gen6{Pb,Sc,Pw,Dd}Enc.lean` fast-path theorems or their kind lines were
opened. Sources: the Go layout in `prysm/ir/ir-mainnet.json` (`go_fields`, gc amd64 offsets), the SSZ layout
of the four containers, the `.S` files of `prysm/go1.26.10/e2e/enc2/link/norm/` (frame, guard, stack slots
touched on the fast path and their contents at the return) and the shape of the committed hand statements
`Prysm.BeaconBlockHeader.Encode.fast_path` / `Prysm.Eth1Data.Encode.fast_path` (binder order and memory order per the
interface text in `enc2/L/OUT.md`).

**Encoder fast path only**: `len(dst) + SizeSSZ ≤ cap(dst)` and every byte-vector field of its exact length.
No growslice branch, no length reject, no morestack path. Not a complete encoder result.

| type | class | frame | guard | memmove |
| --- | --- | --- | --- | --- |
| PowBlock | frame test (`moveSliceNoCapNoScan` test not taken), no `state` word, 3 × bytes 32 | `0x50` | small | yes |
| SyncCommitteeMessage | overlay uint64 (Slot, ValidatorIndex) via stack temps, bytes 32 + 96 | `0xa8` | `0x30` | yes |
| PendingPartialWithdrawal | three uint64 (two overlay) via stack temps, no call | `0x90` | `0x18` | no |
| Deposit_Data | bytes 48 + 32 + uint64 + bytes 96 | `0x88` | `0x10` | yes |

Each statement is an `abbrev … : Prop`; `E2cSame.lean` proves `type_of% generated = this` by `rfl`.
-/

open Machine Runtime TestTarget Codec Prysm.PowBlock.Code
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
    (hmm : MemmoveC S),
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

/-- SyncCommitteeMessage (`state`; Slot `primitives.Slot` at Go 8; BlockRoot `[]byte` 32 at 16; ValidatorIndex
`primitives.ValidatorIndex` at 40; Signature `[]byte` 96 at 48). Frame `0xa8`, guard `lea -0x30(%rsp)`.
Stack: saved rbp, home slots `rsp + 8`, `rsp + 16`; the zeroed 32-byte temp at `rsp − 56` (two 16-byte
halves; Slot stored at `rsp − 56`), `rsp − 112` (capacity), `rsp − 120` (len + 40), `rsp − 24` (pointer), the
temp at `rsp − 88` (ValidatorIndex at `rsp − 88`), `rsp − 16` (pointer), `rsp − 96` (capacity), `rsp − 104`
(len + 144), the `memmove` return slot `rsp − 184` and the scratch. -/
abbrev _root_.Prysm.SyncCommitteeMessage.Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.SyncCommitteeMessage.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.SyncCommitteeMessage.Code.marshalSSZTo k)
    (ast v0 v2 c1 c3 b1 b3 pre d0 d1 d2 d3 : List UInt8)
    (hast : ast.length = 8) (hv0 : v0.length = 8) (hv2 : v2.length = 8) (hc1 : c1.length = 8)
    (hc3 : c3.length = 8) (hb1 : b1.length = 32) (hb3 : b3.length = 96)
    (hd0 : d0.length = 8) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96)
    (p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t56 t40 l112 l120 l24 t88 t72 l16 l96 l104 rslot : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8)
    (ht56 : t56.length = 16) (ht40 : t40.length = 16) (hl112 : l112.length = 8) (hl120 : l120.length = 8)
    (hl24 : l24.length = 8) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hl16 : l16.length = 8)
    (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l112.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq (b1.At p1) ⋆ Eq (b3.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48)) ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hsp : 184 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 144 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 144 ∧ st.data.regs.rcx = s.regs.rdi
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
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 144).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 115)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (b1.At p1) ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- PendingPartialWithdrawal (`state`; Index `primitives.ValidatorIndex` at Go 8, Amount `uint64` at 16,
WithdrawableEpoch `primitives.Epoch` at 24). Frame `0x90`, guard `lea -0x18(%rsp)`, no call on the fast
path. Stack: saved rbp, home slots `rsp + 8`, `rsp + 16`, the zeroed temps at `rsp − 40` (Index) and
`rsp − 72` (WithdrawableEpoch), each two 16-byte halves. Amount is stored from a register. -/
abbrev _root_.Prysm.PendingPartialWithdrawal.Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.marshalSSZTo k)
    (ast v0 v1 v2 pre d0 d1 d2 : List UInt8)
    (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hv2 : v2.length = 8)
    (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t40 t24 t72 t56 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8)
    (ht40 : t40.length = 16) (ht24 : t24.length = 16) (ht72 : t72.length = 16) (ht56 : t56.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (v2.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 24 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 24 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (v2.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- Deposit_Data (`state`; PublicKey `[]byte` 48 at Go 8, WithdrawalCredentials `[]byte` 32 at 32, Amount
`uint64` at 56, Signature `[]byte` 96 at 64). Frame `0x88`, guard `lea -0x10(%rsp)`. Stack: saved rbp, home
slots `rsp + 8`, `rsp + 16`; `rsp − 16` (pointer), `rsp − 40` (len + 48, then len + 184), `rsp − 48`
(capacity), `rsp − 32` (pointer), `rsp − 64` (len + 80), `rsp − 56` (capacity), the `memmove` return slot
`rsp − 152` and the scratch. Amount is stored from a register. -/
abbrev _root_.Prysm.Deposit_Data.Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.Deposit_Data.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.Deposit_Data.Code.marshalSSZTo k)
    (ast v2 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 : List UInt8)
    (hast : ast.length = 8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8)
    (hc3 : c3.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hb3 : b3.length = 96)
    (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l40 l48 l32 l64 l56 rslot : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8)
    (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl32 : l32.length = 8) (hl64 : l64.length = 8)
    (hl56 : l56.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 152)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (b0.At p0) ⋆ Eq (b1.At p1) ⋆ Eq (b3.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88)) ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hsp : 152 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 184 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 184 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (scr : List UInt8), scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 184).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 110)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (b0.At p0) ⋆ Eq (b1.At p1) ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.PowBlock
