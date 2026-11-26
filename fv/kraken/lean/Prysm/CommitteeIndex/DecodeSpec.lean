module

public import Prysm.CommitteeIndex.GeneratedDecodeAccept
public import Prysm.CommitteeIndex.DecodeRejectSize
public import Prysm.CommitteeIndex.SpecDescription
public import Prysm.Epoch.Spec

@[expose] public section

/-!
# Spec alignment of the real CommitteeIndex decoder

The form of `Prysm/Checkpoint/DecodeSpec.lean` for the hand-written `(*primitives.CommitteeIndex).UnmarshalSSZ`.
- `Decode.accept_spec`: if EthLib accepts `bsA` (`desc`) as `v`, there is `x : UInt64` with `v = .uint x`
  and `bsA = uintBytes 8 x`. With these 8 input bytes the machine code returns nil, and the receiver holds
  `uintBytes 8 x` (`Decode.generated_accept`).
- `Decode.reject_size_spec`: `bs.size ≠ 8`: EthLib rejects, and the machine code (with `rcx = bs.size`)
  returns the `fmt.Errorf` error of `Decode.reject_size`.
- `Decode.reject_complete`: every input that EthLib rejects has `size ≠ 8`.
  This is the path condition of the one reject site of `UnmarshalSSZ` (`Decode.reject_size`).
-/

open Machine Runtime Prysm.CommitteeIndex.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.CommitteeIndex

theorem Decode.accept_spec (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize desc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64) (fp s2 c0 : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hc0 : c0.length = 8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (bsA.toList.At s.regs.rbx.toBitVec) ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) :
    ∃ x : UInt64, v = .uint x.toNat ∧ bsA = uintBytes 8 x.toNat ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((uintBytes 8 x.toNat).toList.At s.regs.rbx.toBitVec)
          ⋆ Eq ((uintBytes 8 x.toNat).toList.At s.regs.rax.toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨x, hv, hb⟩ := Prysm.Epoch.uint64_accepted_is_encoding hd
  have hs : bsA.size = 8 := (Prysm.Epoch.uint64_spec_accepts_iff bsA).mp ⟨v, hd⟩
  have h8 : s.regs.rcx = 8 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hs]; rfl
  have hacc := Decode.generated_accept k hk hf bsA.toList (by simp [hs]) s ra guard fp s2 c0 hfp h2 hc0 R h_mem hguard h8
  rw [hb] at hacc
  exact ⟨x, hv, hb, hacc⟩

/-- `len(buf) ≠ 8`: EthLib rejects, and the machine code returns the `fmt.Errorf` error of `Decode.reject_size`. -/
theorem Decode.reject_size_spec (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (bs : Array UInt8) (hbs : bs.size ≠ 8)
    (s : MachineData) (ra guard : UInt64) (fp s2 a40 a24 sp8 sp32 rslot : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (ha40 : a40.length = 16) (ha24 : a24.length = 16)
    (hsp8 : sp8.length = 8) (hsp32 : sp32.length = 32) (hrs : rslot.length = 8)
    (S : Nat) (stk : List UInt8) (hstk : stk.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (a40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (a24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (sp8.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (sp32.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (stk.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ElfData.PrysmTarget.formatBufferLengthReceiced.At ElfData.PrysmTarget.formatBufferLengthReceiced_addr) ⋆ Eq (ElfData.PrysmTarget.boxedEight.At ElfData.PrysmTarget.boxedEight_addr)
      ⋆ StaticBox 8 ⋆ StaticBox s.regs.rcx.toBitVec ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) (hav : 8 + 40 + 40 + 8192 ≤ avail)
    (hct : ConvT64Contract Heap S) (hdd : FmtErrorfDecimalDecimalContract Heap ElfData.PrysmTarget.formatBufferLengthReceiced ElfData.PrysmTarget.typeInt_addr S) :
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb stk' sp' : List UInt8) (av' : Nat), stk'.length = S ∧ sp'.length = 40
          ∧ BoxIn bx s.regs.rcx.toBitVec hb ∧ av' ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ElfData.PrysmTarget.typeInt_addr.toInt ++ Int.toBytes 8 ElfData.PrysmTarget.boxedEight_addr.toInt
              ++ Int.toBytes 8 ElfData.PrysmTarget.typeInt_addr.toInt ++ Int.toBytes 8 bx.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (sp'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 29)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (stk'.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ElfData.PrysmTarget.formatBufferLengthReceiced.At ElfData.PrysmTarget.formatBufferLengthReceiced_addr) ⋆ Eq (ElfData.PrysmTarget.boxedEight.At ElfData.PrysmTarget.boxedEight_addr)
          ⋆ StaticBox 8 ⋆ StaticBox s.regs.rcx.toBitVec ⋆ Eq (hb.At bx) ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨Prysm.Epoch.uint64_spec_rejects bs hbs, Decode.reject_size k hk hf s ra guard fp s2 a40 a24 sp8 sp32 rslot
    hfp h2 ha40 ha24 hsp8 hsp32 hrs S stk hstk Heap avail R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl)) hav hct hdd⟩

omit [Host] in
/-- **`reject_complete`**: every input that EthLib rejects has `size ≠ 8`, the path condition of `Decode.reject_size`. -/
theorem Decode.reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize desc bs = .ok v) :
    bs.size ≠ 8 := fun h8 => h ((Prysm.Epoch.uint64_spec_accepts_iff bs).mpr h8)

end Prysm.CommitteeIndex
