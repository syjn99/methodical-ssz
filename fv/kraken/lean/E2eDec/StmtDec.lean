import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.CheckpointAndEpoch
import Prysm.ElfData.IndexedAttestation
import E2eEnc.Defs
import E2eDec.Code
import E2eDec.Data

/-!
# Hand STATEMENTS of the round-trip decoder `(*v1alpha1.DataColumnsByRootIdentifier).UnmarshalSSZ`

Statements only. Frozen at their commit. A later change needs a new name and a reason; these definitions stay.
Statement shape: `Prysm/IndexedAttestation/Statements.lean`.

    func (c *DataColumnsByRootIdentifier) UnmarshalSSZ(buf []byte) error {              // fulu.ssz.go:1778
        if size < 36 { return ssz.ErrSize }                                              // size reject
        if ReadOffset(buf[32:36]) != 36 { return ssz.ErrInvalidVariableOffset }          // offset reject
        c.BlockRoot = append(make([]byte, 0, 32), buf[0:32]...)                          // makeslice + memmove
        if len(buf[36:]) % 8 != 0 { return fmt.Errorf("misaligned bytes: … %d … %w", …) }    // alignment reject
        if numElem > 128 { return fmt.Errorf("ssz-max exceeded: … %d … %w", …) }            // overflow reject
        c.Columns = make([]uint64, numElem); for i … { c.Columns[i] = LE64(buf[36+8i:]) }    // accept
        return err }

Receiver (IR `go_fields`, size 88): `state` 0, `BlockRoot` 8 (ptr, len, cap), `Columns` 32 (ptr, len, cap). The accept
path writes c + 8 … c + 55. Frame (x = entry rsp): guard `lea -0x10(%rsp),%r12` (`guard + 16 < x`); `push %rbp`;
`sub $0x88` (rsp = x − 144). Spills: x + 8 (rax), x + 16 (rbx), x + 24 (rcx), x + 32 (rdi). Locals: x − 104
(cap − 36), x − 96 (n), x − 88 (buf[36:] pointer), x − 80 (BlockRoot pointer). Callee spill area x − 144 (40 bytes),
runtime call return slot x − 152, scratch `S` below it. The last call on the accept path is the Columns `makeslice` (directive 75).
The alignment reject and the overflow reject run after the BlockRoot allocation and stores; their statements are not in this file.
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz E2eDec.Code E2eEnc
variable [Host]

namespace E2eDec

/-- **Size reject (machine).** `len(buf) < 36`: the decoder returns the two words of `ssz.ErrSize`. -/
def dcd_reject_size_stmt : Prop :=
  ∀ (k : Nat) (hk : DcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcUnmarshal k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat < 36),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Offset reject (machine).** `len(buf) ≥ 36` and the 4 bytes `off` at buf[32:36] are not 36: the decoder returns the two words of `ssz.ErrInvalidVariableOffset`. -/
def dcd_reject_offset_stmt : Prop :=
  ∀ (k : Nat) (hk : DcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcUnmarshal k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (off : List UInt8) (hoff4 : off.length = 4) (hoff : off ≠ dcOff)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (off.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.IndexedAttestation.lvErrInvalidVariableOffset_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset" + 8).toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hlen : 36 ≤ s.regs.rcx.toNat),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (off.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.IndexedAttestation.lvErrInvalidVariableOffset_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset" + 8).toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Accept (machine).** `len(buf) = 36 + 8n`, `n ≤ 128`, offset 36: two `makeslice` calls (BlockRoot 32 bytes, Columns 8n bytes), one `memmove` of the root, the element loop; the decoder returns nil and the receiver holds BlockRoot = (pb, 32, 32) with the root bytes and Columns = (A, n, n) with the input element bytes. `writeBarrier = 0`: the barrier branches are not taken. -/
def dcd_accept_stmt : Prop :=
  ∀ (k : Nat) (hk : DcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcUnmarshal k)
    (n : Nat) (hn : n ≤ 128) (root ib : List UInt8) (hroot : root.length = 32) (hib : ib.length = 8 * n)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s3 s4 l28 l30 l38 l40 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (h4 : s4.length = 8)
    (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hl38 : l38.length = 8) (hl40 : l40.length = 8)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (S : Nat) (hlo : lo.length = S) (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (root.At s.regs.rbx.toBitVec) ⋆ Eq (dcOff.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (ib.At (s.regs.rbx.toBitVec + 36))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = 36 + 8 * n)
    (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hav : 32 + 8 * n ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmsU : MakesliceC Heap ElfData.IndexedAttestation.lvU64Type_addr 8 S)
    (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (pb A : BitVec 64) (l28' l30' l38' l40' spl' lo' : List UInt8),
          l28'.length = 8 ∧ l30'.length = 8 ∧ l38'.length = 8 ∧ l40'.length = 8 ∧ spl'.length = 40 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (l28'.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (l30'.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (l38'.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (l40'.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 76)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - (32 + 8 * n))
          ⋆ Eq (root.At s.regs.rbx.toBitVec) ⋆ Eq (dcOff.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (ib.At (s.regs.rbx.toBitVec + 36))
          ⋆ Eq ((Int.toBytes 8 pb.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 A.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (root.At pb) ⋆ Eq (ib.At A)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Accept (spec).** If EthLib accepts `bsA` as `v`, there is `g : PDc` with `g.toValue = v` and `bsA = pdcEnc g`, and the machine code decodes `bsA` into `g`. -/
def dcd_accept_spec_stmt : Prop :=
  ∀ (k : Nat) (hk : DcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcUnmarshal k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmDcDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s3 s4 l28 l30 l38 l40 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (h4 : s4.length = 8)
    (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hl38 : l38.length = 8) (hl40 : l40.length = 8)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (S : Nat) (hlo : lo.length = S) (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (bsA.toList.At s.regs.rbx.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size)
    (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hav : 32 + 8 * ((bsA.size - 36) / 8) ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmsU : MakesliceC Heap ElfData.IndexedAttestation.lvU64Type_addr 8 S)
    (hmm : MemmoveC S),
    ∃ g : PDc, g.toValue = v ∧ bsA = pdcEnc g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0 ∧
        ∃ (pb A : BitVec 64),
        (Eq (bsA.toList.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 pb.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 A.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 g.cols.length).toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 g.cols.length).toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (g.root.toList.At pb) ⋆ Eq ((Spec.u64Bytes g.cols).toList.At A)
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end E2eDec
