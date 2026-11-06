import Fk.NeAccept
import Fk.NeReject
import Fk.LuErr
import Fv1.SpecNested

/-!
# Nested.UnmarshalSSZ against EthLib (B3)

- `ne_unmarshal_accept_spec_k`: if EthLib accepts `bs` as `v`, there is a Go
  value `g` (`g.l` has at most 16 elements) with `g.toValue = v`, and the
  machine code returns nil with A, the new S object and the new L object
  holding `g` in Go layout.
- `ne_spec_accepts_iff`: EthLib accepts exactly when every Go check passes:
  Nested's own (`len ≥ 28`, offset = 28), the Scalars bool byte (byte 23
  ≤ 1, checked inside Scalars.UnmarshalSSZ) and the four ListU64 checks on
  `buf[28:]` (inside ListU64.UnmarshalSSZ).
- `ne_reject_short_spec`, `ne_reject_offset_spec`: the two Nested checks,
  EthLib's rejection and the machine's error together. The callee checks
  return through `fmt.Errorf("S: %w")` / `("L: %w")`; those wrap paths are
  not proved (REPORT-1b).

Premises the Go caller provides: see `ne_accept_main` (in `Fk/NeAccept.lean`).
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz

abbrev NeG := { g : NestedG // g.ok }

theorem ne_toValue_surjective' (v : Value) (h : Value.fits neDesc v = true) :
    ∃ g : NeG, g.1.toValue = v := by
  obtain ⟨g, hg, rfl⟩ := ne_toValue_surjective v h
  exact ⟨⟨g, hg⟩, rfl⟩

theorem ne_accepted (bs : Array UInt8) (v : Value) (hd : deserialize neDesc bs = .ok v) :
    ∃ g : NestedG, g.ok ∧ g.toValue = v ∧ bs = neEncode g := by
  obtain ⟨⟨g, hg⟩, rfl, rfl⟩ := accepted_is_enc (G := NeG) (toV := fun g => g.1.toValue)
    (enc := fun g => neEncode g.1) neDesc_wellFormed (fun g => ne_serialize g.1 g.2)
    ne_toValue_surjective' hd
  exact ⟨g, hg, rfl, rfl⟩

theorem ne_deserialize_enc (g : NestedG) (hg : g.ok) : deserialize neDesc (neEncode g) = .ok g.toValue :=
  deserialize_enc (G := NeG) (toV := fun g => g.1.toValue) (enc := fun g => neEncode g.1)
    neDesc_wellFormed (fun g => ne_serialize g.1 g.2) (fun g => ne_toValue_fits g.1 g.2) ⟨g, hg⟩

theorem ne_readOffset (g : NestedG) : readUint (neEncode g) 24 4 = 28 := by
  have hf : (uintBytes 8 g.a.toNat ++ scEncode g.s).size = 24 := by
    simp [Fv.uintBytes_size, sc_encode_size]
  have := readUint_append (uintBytes 8 g.a.toNat ++ scEncode g.s) (uintBytes 4 28 ++ luEncode g.l) 0 4
  rw [hf, readUint_uintBytes_prefix _ 4 28 (by decide)] at this
  simpa [neEncode, Array.append_assoc] using this

/-- Each failing Nested check makes EthLib reject. -/
theorem ne_spec_rejects (bs : Array UInt8) (h : bs.size < 28 ∨ readUint bs 24 4 ≠ 28) :
    ∃ e, deserialize neDesc bs = .error e := by
  cases hd : deserialize neDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v =>
    obtain ⟨g, -, -, rfl⟩ := ne_accepted bs v hd
    have := ne_encode_size g
    rcases h with h | h
    · omega
    · exact absurd (ne_readOffset g) h

theorem ext_app (a b : Array UInt8) : (a ++ b).extract a.size (a ++ b).size = b := by
  apply Array.ext <;> simp

theorem ext_join (bs : Array UInt8) (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) :
    bs.extract a b ++ bs.extract b c = bs.extract a c := by
  rw [Array.extract_append_extract, Nat.min_eq_left h1, Nat.max_eq_right h2]

/-- The checks the Go code makes on a Nested input, its own and its callees'
(Scalars: the bool byte; ListU64: `luChecks` on `buf[28:]`). -/
def neChecks (bs : Array UInt8) : Prop :=
  28 ≤ bs.size ∧ readUint bs 24 4 = 28 ∧ readUint bs 23 1 ≤ 1 ∧ luChecks (bs.extract 28 bs.size)

theorem ne_tail (g : NestedG) : (neEncode g).extract 28 (neEncode g).size = luEncode g.l := by
  have hf : (uintBytes 8 g.a.toNat ++ scEncode g.s ++ uintBytes 4 28).size = 28 := by
    simp [Fv.uintBytes_size, sc_encode_size]
  have := ext_app (uintBytes 8 g.a.toNat ++ scEncode g.s ++ uintBytes 4 28) (luEncode g.l)
  rw [hf] at this
  exact this

theorem bool_bytes (e : Bool) : (#[if e then 1 else 0] : Array UInt8) = uintBytes 1 (if e then 1 else 0) := by
  cases e <;> decide

theorem ne_bool (g : NestedG) : readUint (neEncode g) 23 1 ≤ 1 := by
  have hf : (uintBytes 8 g.a.toNat ++ uintBytes 1 g.s.a.toNat ++ uintBytes 2 g.s.b.toNat ++ uintBytes 4 g.s.c.toNat
      ++ uintBytes 8 g.s.d.toNat).size = 23 := by simp [Fv.uintBytes_size]
  have := readUint_append (uintBytes 8 g.a.toNat ++ uintBytes 1 g.s.a.toNat ++ uintBytes 2 g.s.b.toNat
      ++ uintBytes 4 g.s.c.toNat ++ uintBytes 8 g.s.d.toNat)
    (uintBytes 1 (if g.s.e then 1 else 0) ++ (uintBytes 4 28 ++ luEncode g.l)) 0 1
  rw [hf, readUint_uintBytes_prefix _ 1 _ (by split <;> decide)] at this
  have e : neEncode g = uintBytes 8 g.a.toNat ++ uintBytes 1 g.s.a.toNat ++ uintBytes 2 g.s.b.toNat
      ++ uintBytes 4 g.s.c.toNat ++ uintBytes 8 g.s.d.toNat
      ++ (uintBytes 1 (if g.s.e then 1 else 0) ++ (uintBytes 4 28 ++ luEncode g.l)) := by
    simp only [neEncode, scEncode, bool_bytes, Array.append_assoc]
  rw [e, this]; split <;> decide

theorem neEncode_checks (g : NestedG) (hg : g.ok) : neChecks (neEncode g) := by
  have := ne_encode_size g
  refine ⟨by omega, ne_readOffset g, ne_bool g, ?_⟩
  rw [ne_tail]; exact luEncode_checks g.l hg

theorem ne_checks_enc (bs : Array UInt8) (h : neChecks bs) : ∃ g : NestedG, g.ok ∧ bs = neEncode g := by
  obtain ⟨h28, hoff, hb, hl⟩ := h
  obtain ⟨h4, hlo, hmod, hn⟩ := hl
  simp only [Array.size_extract] at h4 hmod hn
  obtain ⟨l, hlok, hle⟩ := lu_checks_enc _ ((bs.size - 28 - 4) / 8) (by simp; omega) (by omega) hlo
  have r8 := readUint_lt bs 0 8; have r1 := readUint_lt bs 8 1; have r2 := readUint_lt bs 9 2
  have r4 := readUint_lt bs 11 4; have r8' := readUint_lt bs 15 8
  refine ⟨⟨UInt64.ofNat (readUint bs 0 8),
    ⟨UInt8.ofNat (readUint bs 8 1), UInt16.ofNat (readUint bs 9 2), UInt32.ofNat (readUint bs 11 4),
      UInt64.ofNat (readUint bs 15 8), readUint bs 23 1 == 1⟩, l⟩, hlok, ?_⟩
  have r1' := readUint_lt bs 23 1
  have hbool : #[if (readUint bs 23 1 == 1) = true then (1 : UInt8) else 0] = bs.extract 23 24 := by
    rw [← uintBytes_readUint_slice bs 23 1 (by omega)]
    simp only [Nat.reducePow, Nat.reduceMul] at r1'
    have : readUint bs 23 1 = 0 ∨ readUint bs 23 1 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  have e24 := uintBytes_readUint_slice bs 24 4 (by omega)
  rw [hoff] at e24
  simp only [Nat.reduceAdd] at e24
  simp only [neEncode, scEncode, ← hle, hbool, ← e24]
  simp only [Nat.reducePow, Nat.reduceMul] at r8 r1 r2 r4 r8'
  rw [UInt64.toNat_ofNat_of_lt' r8, UInt8.toNat_ofNat_of_lt' r1, UInt16.toNat_ofNat_of_lt' r2,
    UInt32.toNat_ofNat_of_lt' r4, UInt64.toNat_ofNat_of_lt' r8',
    uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 8 1 (by omega),
    uintBytes_readUint_slice bs 9 2 (by omega), uintBytes_readUint_slice bs 11 4 (by omega),
    uintBytes_readUint_slice bs 15 8 (by omega)]
  simp only [Nat.zero_add, Nat.reduceAdd, e24, Array.extract_append_extract]
  rw [show min 8 9 = 8 from rfl, show max 9 11 = 11 from rfl, ext_join bs 8 11 15 (by omega) (by omega),
    ext_join bs 8 15 23 (by omega) (by omega), ext_join bs 8 23 24 (by omega) (by omega),
    ext_join bs 0 8 24 (by omega) (by omega), ext_join bs 0 24 28 (by omega) (by omega),
    ext_join bs 0 28 bs.size (by omega) (by omega)]
  simp

/-- EthLib accepts a Nested input exactly when every Go check passes (Nested's
own two, the Scalars bool byte, the four ListU64 checks on `buf[28:]`). -/
theorem ne_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize neDesc bs = .ok v) ↔ neChecks bs := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, hg, -, rfl⟩ := ne_accepted bs v hd
    exact neEncode_checks g hg
  · intro h
    obtain ⟨g, hg, rfl⟩ := ne_checks_enc bs h
    exact ⟨_, ne_deserialize_enc g hg⟩

variable [Host]

set_option maxHeartbeats 2000000 in
theorem ne_unmarshal_accept_spec_k (k : Nat) (hk : NestedUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedUnmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize neDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp x8 x16 x24 x32 l56 l48 rslot cspill blk cA cS cL : List UInt8)
    (hfp : fp.length = 8) (hx8 : x8.length = 8) (hx16 : x16.length = 8) (hx24 : x24.length = 8)
    (hx32 : x32.length = 8) (hl56 : l56.length = 8) (hl48 : l48.length = 8) (hrs : rslot.length = 8)
    (hcs : cspill.length = 16) (S : Nat) (hS : S < 2 ^ 60) (hblk : blk.length = 144 + S)
    (hcA : cA.length = 8) (hcS : cS.length = 8) (hcL : cL.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat)
    (P : ∀ g : NestedG, g.ok → bsA = neEncode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (x8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (x16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (x24.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (x32.At (s.regs.rsp.toBitVec + 32)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (cspill.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (blk.At (s.regs.rsp.toBitVec - 104 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ((uintBytes 8 g.a.toNat).toList.At s.regs.rbx.toBitVec)
      ⋆ Eq ((scField g.s 0).At (s.regs.rbx.toBitVec + 8)) ⋆ Eq ((scField g.s 1).At (s.regs.rbx.toBitVec + 8 + 1))
      ⋆ Eq ((scField g.s 2).At (s.regs.rbx.toBitVec + 8 + 3)) ⋆ Eq ((scField g.s 3).At (s.regs.rbx.toBitVec + 8 + 7))
      ⋆ Eq ((scField g.s 4).At (s.regs.rbx.toBitVec + 8 + 15))
      ⋆ Eq ([28, 0, 0, 0].At (s.regs.rbx.toBitVec + 24))
      ⋆ Eq ([4, 0, 0, 0].At (s.regs.rbx.toBitVec + 28)) ⋆ Eq ((u64Bytes g.l.l).toList.At (s.regs.rbx.toBitVec + 28 + 4))
      ⋆ Eq (cA.At s.regs.rax.toBitVec) ⋆ Eq (cS.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hsp : 104 + 144 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bsA.size) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hav : 24 + 24 + 8 * 16 ≤ avail)
    (hnoS : NewobjectC Heap (label "type__" + 135104).toBitVec 24 (144 + S))
    (hnoL : NewobjectC Heap (label "type__" + 83104).toBitVec 24 (144 + S))
    (hsc : ScUAccC) (hlu : LuUAccC Heap S) :
    ∃ g : NestedG, g.ok ∧ g.toValue = v ∧ bsA = neEncode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧
        ∃ ps pl p : BitVec 64, (Eq ((uintBytes 8 g.a.toNat).toList.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 pl.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((scField g.s 0).At ps) ⋆ Eq ((scField g.s 1).At (ps + 2)) ⋆ Eq ((scField g.s 2).At (ps + 4))
          ⋆ Eq ((scField g.s 3).At (ps + 8)) ⋆ Eq ((scField g.s 4).At (ps + 16))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At pl) ⋆ Eq ((Int.toBytes 8 (g.l.l.length : Int)).At (pl + 8))
          ⋆ Eq ((Int.toBytes 8 (g.l.l.length : Int)).At (pl + 16)) ⋆ Eq ((u64Bytes g.l.l).toList.At p)
          ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, hg, rfl, rfl⟩ := ne_accepted bsA v hd
  refine ⟨g, hg, rfl, rfl, ?_⟩
  exact ne_accept_main k hk hf (uintBytes 8 g.a.toNat).toList (by simp [Fv.uintBytes_size]) g.s g.l hg s ra guard
    fp x8 x16 x24 x32 l56 l48 rslot cspill blk cA cS cL hfp hx8 hx16 hx24 hx32 hl56 hl48 hrs hcs S hS hblk
    hcA hcS hcL R Heap avail (P g hg rfl) hguard hsp (by rw [hlen, ne_encode_size]) hcap hcap63 hav hnoS hnoL hsc hlu

/-- `len(buf) < 28`: EthLib rejects, and the machine returns `ssz.ErrSize`. -/
theorem ne_reject_short_spec (k : Nat) (hk : NestedUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedUnmarshalSSZ k) (bs : Array UInt8) (hbs : bs.size < 28)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize neDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨ne_spec_rejects bs (.inl hbs),
    ne_reject_short_main k hk hf s ra guard e0 e1 fp slot hfp hsl R h_mem hguard (by omega)⟩

/-- `len(buf) ≥ 28` and the offset at bytes 24..27 ≠ 28: EthLib rejects, and the
machine returns `ssz.ErrInvalidVariableOffset`. The input chunk `o4` is the
four bytes the code loads (`bs[24:28]`). -/
theorem ne_reject_offset_spec (k : Nat) (hk : NestedUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedUnmarshalSSZ k) (bs : Array UInt8) (h28 : 28 ≤ bs.size) (hoff : readUint bs 24 4 ≠ 28)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (((bs.toList.drop 24).take 4).At (s.regs.rbx.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize neDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨ne_spec_rejects bs (.inr hoff),
    ne_reject_offset_main k hk hf s ra guard e0 e1 fp slot hfp hsl _ (by simp; omega)
      (by rw [ofBytes_readUint bs 4 24 (by omega)]; exact_mod_cast hoff) R h_mem hguard (by omega)⟩
