import Fk.LcReject
import Fk.LuErr
import Fv1.SpecListC

/-!
# ListC.UnmarshalSSZ rejections against EthLib (B3)

`lc_accepted`: every input EthLib accepts is `lcEncode g` for a `g` with at
most 4 elements, each with at most 16 words. From the shape of `lcEncode`:
the container offset is 4; the list bytes are empty (no element) or at least
8 bytes; the first element offset is `4n ≠ 0`, at most the list length.
`lc_spec_rejects`: each Go check that fails makes EthLib reject.
`lc_reject_*_spec`: the machine theorem and EthLib's rejection together.
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz

abbrev LcG := { g : ListCG // g.ok }

theorem lc_toValue_surjective' (v : Value) (h : Value.fits lcDesc v = true) :
    ∃ g : LcG, g.1.toValue = v := by
  obtain ⟨g, hg, rfl⟩ := lc_toValue_surjective v h
  exact ⟨⟨g, hg⟩, rfl⟩

theorem lc_accepted (bs : Array UInt8) (v : Value) (hd : deserialize lcDesc bs = .ok v) :
    ∃ g : ListCG, g.ok ∧ g.toValue = v ∧ bs = lcEncode g := by
  obtain ⟨⟨g, hg⟩, rfl, rfl⟩ := accepted_is_enc (G := LcG) (toV := fun g => g.1.toValue)
    (enc := fun g => lcEncode g.1) lcDesc_wellFormed (fun g => lc_serialize g.1 g.2)
    lc_toValue_surjective' hd
  exact ⟨g, hg, rfl, rfl⟩

theorem lu_bodies_ge : ∀ (items : List ListU64),
    4 * items.length ≤ (bodiesOf (offsetSlots (items.map luEncode))).size
  | [] => by simp
  | x :: rest => by
    have h1 := lu_encode_size x
    have := lu_bodies_ge rest
    simp only [List.map_cons, offsetSlots_cons, bodiesOf, Array.size_append, List.length_cons]
    omega

theorem lc_shape (g : ListCG) (hg : g.ok) :
    (lcEncode g).size = 4 + (lcBody g).size ∧ readUint (lcEncode g) 0 4 = 4 ∧
    (g.items = [] → (lcBody g).size = 0) ∧
    (g.items ≠ [] → 8 ≤ (lcBody g).size ∧ readUint (lcEncode g) 4 4 = 4 * g.items.length
      ∧ 4 * g.items.length ≤ (lcBody g).size) := by
  have hsz : (lcEncode g).size = 4 + (lcBody g).size := by simp [lcEncode, Fv.uintBytes_size]
  have hbody : (lcBody g).size = 4 * g.items.length + (bodiesOf (offsetSlots (g.items.map luEncode))).size := by
    simp [lcBody, lcParts, headOf_offsetSlots_size]
  have hge := lu_bodies_ge g.items
  refine ⟨hsz, by simp only [lcEncode]; exact readUint_uintBytes_prefix _ 4 4 (by decide), ?_, ?_⟩
  · intro h; rw [hbody, h]; simp [bodiesOf]
  · intro hne
    have hpos : 1 ≤ g.items.length := by
      cases h : g.items with
      | nil => exact absurd h hne
      | cons _ _ => simp
    refine ⟨by omega, ?_, by omega⟩
    have hb := lcBody_size_le g hg
    have := readUint_headOf_offset (g.items.map luEncode) (4 * g.items.length) (uintBytes 4 4)
      (bodiesOf (offsetSlots (g.items.map luEncode))) 0 (by simp; omega)
      (by rw [bodyWidth_offsetSlots]; simp only [bytesPerOffset]; omega)
    simp only [Fv.uintBytes_size, Nat.zero_mul, Nat.add_zero, bytesPerOffset] at this
    simp only [lcEncode, lcBody, lcParts]
    rw [this]
    cases h : g.items with
    | nil => exact absurd h hne
    | cons x rest => simp [h, runningOffsets]

/-- Each failing Go check (in the order of the code) makes EthLib reject. -/
theorem lc_spec_rejects (bs : Array UInt8)
    (h : bs.size < 4 ∨ readUint bs 0 4 ≠ 4 ∨ (5 ≤ bs.size ∧ bs.size ≤ 7)
      ∨ (8 ≤ bs.size ∧ readUint bs 4 4 = 0) ∨ (8 ≤ bs.size ∧ bs.size - 4 < readUint bs 4 4)) :
    ∃ e, deserialize lcDesc bs = .error e := by
  cases hd : deserialize lcDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v =>
    exfalso
    obtain ⟨g, hg, -, rfl⟩ := lc_accepted bs v hd
    obtain ⟨hsz, h0, he, hne⟩ := lc_shape g hg
    by_cases hi : g.items = []
    · have := he hi; rcases h with h | h | h | h | h <;> omega
    · obtain ⟨h8, h4, hle⟩ := hne hi
      have : 1 ≤ g.items.length := by
        cases hh : g.items with
        | nil => exact absurd hh hi
        | cons _ _ => simp
      rcases h with h | h | h | h | h <;> omega

variable [Host]

/-- `len < 4`: EthLib rejects; the machine returns `ssz.ErrSize`. -/
theorem lc_reject_short_spec (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k) (bs : Array UInt8) (hbs : bs.size < 4)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize lcDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨lc_spec_rejects bs (.inl hbs),
    lc_reject_short_main k hk hf s ra guard e0 e1 fp slot hfp hsl R h_mem hguard (by omega)⟩

/-- `len ≥ 4`, container offset ≠ 4: EthLib rejects; the machine returns
`ssz.ErrInvalidVariableOffset`. The chunk the code loads is `bs[0:4]`. -/
theorem lc_reject_offset_spec (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k) (bs : Array UInt8) (h4 : 4 ≤ bs.size) (hoff : readUint bs 0 4 ≠ 4)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (((bs.toList.drop 0).take 4).At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize lcDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨lc_spec_rejects bs (.inr (.inl hoff)),
    lc_reject_offset_main k hk hf s ra guard e0 e1 fp slot hfp hsl _ (by simp; omega)
      (by rw [ofBytes_readUint bs 4 0 (by omega)]; exact_mod_cast hoff) R h_mem hguard (by omega)⟩

/-- `5 ≤ len ≤ 7`: EthLib rejects; the machine returns a non-nil error. -/
theorem lc_reject_tail_spec (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k) (bs : Array UInt8) (h5 : 5 ≤ bs.size) (h7 : bs.size ≤ 7)
    (s : MachineData) (ra guard : UInt64) (fp slot rslot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 232)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 232 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 232 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bs.size) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hfe : FmtErrorfC Heap S) :
    (∃ e, deserialize lcDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨lc_spec_rejects bs (.inr (.inr (.inl ⟨h5, h7⟩))),
    lc_reject_tail_main k hk hf s ra guard fp slot rslot hfp hsl hrs R S scratch hsc Heap avail h_mem hguard hsp
      (by omega) (by omega) hcap hcap63 hfe⟩

/-- `len ≥ 8`, first element offset 0: EthLib rejects; the machine returns a
non-nil error. The chunk the code loads is `bs[4:8]`. -/
theorem lc_reject_zero_spec (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k) (bs : Array UInt8) (h8 : 8 ≤ bs.size) (h0 : readUint bs 4 4 = 0)
    (s : MachineData) (ra guard : UInt64) (fp slot rslot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 232)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 232 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq (((bs.toList.drop 4).take 4).At (s.regs.rbx.toBitVec + 4)) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 232 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bs.size) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hfe : FmtErrorfC Heap S) :
    (∃ e, deserialize lcDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨lc_spec_rejects bs (.inr (.inr (.inr (.inl ⟨h8, h0⟩)))),
    lc_reject_zero_main k hk hf s ra guard fp slot rslot hfp hsl hrs _ (by simp; omega)
      (by rw [ofBytes_readUint bs 4 4 (by omega), h0]; rfl) R S scratch hsc Heap avail h_mem hguard hsp
      (by omega) hcap hcap63 hfe⟩

/-- `len ≥ 8`, first element offset `o` (≠ 0, multiple of 4, ≤ 16) past the
end of the list bytes: EthLib rejects; the machine returns a non-nil error. -/
theorem lc_reject_past_spec (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k) (bs : Array UInt8) (h8 : 8 ≤ bs.size)
    (ho0 : readUint bs 4 4 ≠ 0) (ho4 : readUint bs 4 4 % 4 = 0) (ho16 : readUint bs 4 4 ≤ 16)
    (hpast : bs.size - 4 < readUint bs 4 4)
    (s : MachineData) (ra guard : UInt64) (fp slot rslot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 232)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 232 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq (((bs.toList.drop 4).take 4).At (s.regs.rbx.toBitVec + 4)) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 232 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bs.size) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hfe : FmtErrorfC Heap S) :
    (∃ e, deserialize lcDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨lc_spec_rejects bs (.inr (.inr (.inr (.inr ⟨h8, hpast⟩)))),
    lc_reject_past_main k hk hf s ra guard fp slot rslot hfp hsl hrs _ (by simp; omega)
      (readUint bs 4 4) (ofBytes_readUint bs 4 4 (by omega)) ho0 ho4 ho16 R S scratch hsc Heap avail h_mem hguard hsp
      (by omega) (by omega) hcap hcap63 hfe⟩
