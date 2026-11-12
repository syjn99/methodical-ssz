import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import E2e.Data
import E2e.Code
import E2eScal.BhCode
import E2eScal.H4Code

/-!
# Independent hand STATEMENTS of the two accept theorems (hold-out; statements only, no proof)

Hand-written BEFORE the proof generator (`gen/scal/scalgen.py`) was run on
either type and before any generator output for them was read.
Sources: the Go receiver layout (IR `go_fields` in `prysm/ir/ir-mainnet.json`), the SSZ layout
(consensus-specs; `DdDesc.lean`, `PwDesc.lean`), the frame facts of the two `.S` files
(`prysm/go1.26.10/e2e/h4/link/norm`), and the statement shape of the earlier hand accept theorems
`E2eScal.Bi.bi_e2e_accept_main`, `E2eScal.Dm.dm_e2e_accept_main`, `E2eScal.E1.e1_e2e_accept_main` and
(for the callee form) `E2eScal.Bh.bh_e2e_accept_main`. These abbrevs are the targets of the
`--same-as-prop` identity check and of the hand proofs. They are not generator output.

## `dd_accept_stmt` — `(*v1alpha1.Deposit_Data).UnmarshalSSZ`

    func (d *Deposit_Data) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 184 { return ssz.ErrSize }
        d.PublicKey = append(make([]byte, 0, 48), buf[0:48]...)
        d.WithdrawalCredentials = append(make([]byte, 0, 32), buf[48:80]...)
        d.Amount = ssz.UnmarshallUint64(buf[80:88])
        d.Signature = append(make([]byte, 0, 96), buf[88:184]...)
        return err }

Receiver: protoc struct, IR `go_fields` (size 120): `state` 0, `PublicKey` 8 (ptr, len, cap), `WithdrawalCredentials`
32, `Amount` 56, `Signature` 64, `unknownFields` 88, `sizeCache` 112 (the last two in `R`).
Frame (`.S`): `sub $0x20`; spills `0x30(%rsp)` = entry rsp + 8 (rax), `0x38(%rsp)` = entry rsp + 16 (rbx);
`0x18(%rsp)` = entry rsp − 16 (slice pointer save `l18`); `0x0…0x17(%rsp)` = entry rsp − 40 (24 bytes, `spl`);
runtime call return slot entry rsp − 48; `lo` = the `S` bytes below it. Three makeslice / memmove calls,
176 heap bytes; the last runtime call (memmove of Signature) is directive 105, so its return address is
directive 106.

## `pw_accept_stmt` — `(*v1alpha1.PendingPartialWithdrawal).UnmarshalSSZ`

    func (p *PendingPartialWithdrawal) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 24 { return ssz.ErrSize }
        if err = p.Index.UnmarshalSSZ(buf[0:8]); err != nil { return fmt.Errorf("Index: %w", err) }
        p.Amount = ssz.UnmarshallUint64(buf[8:16])
        if err = p.WithdrawableEpoch.UnmarshalSSZ(buf[16:24]); err != nil { return fmt.Errorf(...) }
        return err }

Receiver: protoc struct, IR `go_fields` (size 64): `state` 0, `Index` 8, `Amount` 16, `WithdrawableEpoch` 24,
`unknownFields` 32, `sizeCache` 56 (the last two in `R`).
Frame (`.S`): `sub $0x48`; spills `0x58(%rsp)` = entry rsp + 8 (rax), `0x60(%rsp)` = + 16 (rbx), `0x70(%rsp)` = + 32
(rdi). The two callees (ValidatorIndex, Epoch; leaf functions, function specs `ViUAccC` / `EpUAccC`) have their
return slot at entry rsp − 88, save rbp at entry rsp − 96 (`lo`) and spill their rbx to entry rsp − 72 (`sp1`).
The callees check the stack guard at entry rsp − 88, hence `guard + 88 < rsp`. The Epoch call is directive
59, so the return slot holds directive 60 at the end. Error-path frame slots are untouched on this path (in `R`).
-/

open Machine Runtime TestTarget E2e E2eScal.H4Code E2eScal.BhCode
variable [Host]

namespace E2eScal.H4

/-- Hand statement of the accept path of `(*v1alpha1.Deposit_Data).UnmarshalSSZ`: on a 184-byte input it
returns nil and the receiver holds fresh PublicKey (48) / WithdrawalCredentials (32) / Signature (96) slices
equal to buf[0:48] / buf[48:80] / buf[88:184] (len = cap) and Amount = buf[80:88]; input, `state`, the caller's
frame `R` and the stack guard are unchanged; 176 heap bytes are used. -/
abbrev dd_accept_stmt : Prop :=
  ∀ (k : Nat) (hk : DdUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DdUnmarshal k)
    (pk wc amt sig : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8)
    (hsig : sig.length = 96)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 aN aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8) (haN : aN.length = 8)
    (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
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
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aN.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64)) ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 184) (hav : 176 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
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
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72)) ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (pk.At p1) ⋆ Eq (wc.At p2) ⋆ Eq (sig.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- Hand statement of the accept path of `(*v1alpha1.PendingPartialWithdrawal).UnmarshalSSZ`: on a 24-byte
input it returns nil and the receiver holds Index = buf[0:8], Amount = buf[8:16], WithdrawableEpoch =
buf[16:24]; input, `state`, the spills, the caller's frame `R` and the stack guard are unchanged. The two
delegated fields go through the callees' code (`ViUnmarshal`, `EpUnmarshal` placed in the host). -/
abbrev pw_accept_stmt : Prop :=
  ∀ (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k)
    (kV : Nat) (hkV : ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh ViUnmarshal kV)
    (kE : Nat) (hkE : E2e.Code.EpUnmarshal.IsInfixAt Host.prog kE) (hfE : LabelsFresh E2e.Code.EpUnmarshal kE)
    (in0 in1 in2 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8) (hin2 : in2.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lo ast a8 a16 a24 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp1 : sp1.length = 8) (hrs : rslot.length = 8) (hlo : lo.length = 8)
    (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8) (ha24 : a24.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (in2.At (s.regs.rbx.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (a24.At (s.regs.rax.toBitVec + 24)) ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 24),
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
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 60)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in2.At (s.regs.rbx.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (in2.At (s.regs.rax.toBitVec + 24)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end E2eScal.H4
