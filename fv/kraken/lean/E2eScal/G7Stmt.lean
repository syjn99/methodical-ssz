import Fk.Contracts
import Fk.Frame
import Fk.Bytes
import Fk.Labels
import E2e.Data
import E2e.Code
import E2eScal.KindEncN
import E2eScal.F24Code

/-!
# Independent hand STATEMENTS of two decoder accept paths and two encoder fast paths with a
20-byte vector field (statements only, no proof)

Hand-written BEFORE the generators were changed for the 20-byte kind, so before any
generated theorem of these four functions existed (the one-shot runs on the 24 flat types refused all four: "new field kind (b20)").
Sources: the Go receiver layout (IR `go_fields` of `prysm/ir/ir-mainnet.json`, gc amd64 offsets), the SSZ layout
(field sizes in IR order), the `.S` files of `prysm/go1.26.10/e2e/f24/link/norm/` (frame, guard, spills, stack slots
touched on the path and their contents at the return, the directive of the last call), the statement shape of the
committed hand statements `E2eScal.F24.dpr_accept_stmt` (decoders, frame `0x20`, no callee) and
`E2eScal.E2c.dd_hand_fast`, `E2eScal.F24.vid_hand_fast` (encoders), and the interface text of `enc2/L/OUT.md` (chunk order: saved
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
-/

open Fk E2e E2e.Code E2eScal.F24Code
variable [Host]

namespace E2eScal.G7

/-- Hand statement of the accept path of `(*v1.BuilderExitRequest).UnmarshalSSZ`: on a 68-byte input it returns nil
and the receiver holds fresh SourceAddress (20) / Pubkey (48) slices equal to buf[0:20] / buf[20:68] (len = cap);
input, `state`, the spills, the caller's frame `R` and the stack guard are unchanged; 68 heap bytes are used. -/
abbrev ber_accept_stmt : Prop :=
  ∀ (k : Nat) (hk : BerUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BerUnmarshal k)
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
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
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

/-- Hand statement of the accept path of `(*v1.WithdrawalRequest).UnmarshalSSZ`: on a 76-byte input it returns nil
and the receiver holds fresh SourceAddress (20) / ValidatorPubkey (48) slices equal to buf[0:20] / buf[20:68]
(len = cap) and Amount = buf[68:76]; input, `state`, the spills, the caller's frame `R` and the stack guard are
unchanged; 68 heap bytes are used. -/
abbrev wdr_accept_stmt : Prop :=
  ∀ (k : Nat) (hk : WdrUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh WdrUnmarshal k)
    (sa pk amt : List UInt8) (hsa : sa.length = 20) (hpk : pk.length = 48) (hamt : amt.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 aN : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8) (haN : aN.length = 8)
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
      ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 68))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aN.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 76) (hav : 68 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
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
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 68))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 40)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (sa.At p1) ⋆ Eq (pk.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- BLSToExecutionChange encoder fast path (`state`; ValidatorIndex `primitives.ValidatorIndex` at Go 8,
FromBlsPubkey `[]byte` 48 at 16, ToExecutionAddress `[]byte` 20 at 40). Frame `0x70`, small guard; stack: saved rbp,
home slots `rsp + 8`, `rsp + 16`; the zeroed temp `rsp − 72` / `rsp − 56` (ValidatorIndex at − 72); `rsp − 32`
(capacity, then len + 76), `rsp − 40` (len + 56, then capacity), `rsp − 16` (pointer); the `memmove` return slot
`rsp − 128` and the scratch. -/
abbrev btc_hand_fast : Prop :=
  ∀ (k : Nat) (hk : BtcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BtcMarshal k)
    (ast v0 c1 c2 b1 b2 pre d0 d1 d2 : List UInt8)
    (hast : ast.length = 8) (hv0 : v0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8)
    (hb1 : b1.length = 48) (hb2 : b2.length = 20)
    (hd0 : d0.length = 8) (hd1 : d1.length = 48) (hd2 : d2.length = 20)
    (p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t72 t56 l32 l40 l16 rslot : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8)
    (ht72 : t72.length = 16) (ht56 : t56.length = 16) (hl32 : l32.length = 8) (hl40 : l40.length = 8)
    (hl16 : l16.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (b1.At p1) ⋆ Eq (b2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 128 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 76 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 76 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 scr : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 76).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 92)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b1.At p1) ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- ValidatorRegistrationV1 encoder fast path (`state`; FeeRecipient `[]byte` 20 at Go 8, GasLimit `uint64` at 32,
Timestamp `uint64` at 40, Pubkey `[]byte` 48 at 48). Frame `0x88`, guard `lea -0x10(%rsp)`. Stack: saved rbp, home
slots `rsp + 8`, `rsp + 16`; `rsp − 24` (pointer), `rsp − 56` (len + 20), `rsp − 48` (capacity), `rsp − 32`
(len + 84), `rsp − 40` (capacity), `rsp − 16` (pointer), the `memmove` return slot `rsp − 152` and the scratch.
GasLimit and Timestamp are stored from a register. -/
abbrev vr1_hand_fast : Prop :=
  ∀ (k : Nat) (hk : Vr1Marshal.IsInfixAt Host.prog k) (hf : LabelsFresh Vr1Marshal k)
    (ast v1 v2 c0 c3 b0 b3 pre d0 d1 d2 d3 : List UInt8)
    (hast : ast.length = 8) (hv1 : v1.length = 8) (hv2 : v2.length = 8) (hc0 : c0.length = 8)
    (hc3 : c3.length = 8) (hb0 : b0.length = 20) (hb3 : b3.length = 48)
    (hd0 : d0.length = 20) (hd1 : d1.length = 8) (hd2 : d2.length = 8) (hd3 : d3.length = 48)
    (p0 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l24 l56 l48 l32 l40 l16 rslot : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl24 : l24.length = 8)
    (hl56 : l56.length = 8) (hl48 : l48.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8)
    (hl16 : l16.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 152)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 56)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq (b0.At p0) ⋆ Eq (b3.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36)) ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hsp : 152 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 84 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 84 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (scr : List UInt8), scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 20).toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 84).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 93)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 56)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (b0.At p0) ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end E2eScal.G7
