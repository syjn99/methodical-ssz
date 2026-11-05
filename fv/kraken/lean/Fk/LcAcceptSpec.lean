import Fk.LcAccept
import Fk.LcSpec
import Fk.LcSize

/-!
# ListC accept path against EthLib

From `deserialize lcDesc bs = .ok v`: `bs = lcEncode g` (`lc_accepted`), so
the list bytes `tl = lcBody g` are the offset table (offset of element j =
4n + the sizes before j) and then the element encodings. `lc_tl_shape` gives
the premises of `lc_accept_main` in that form.
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz

/-- The offset table as a list. -/
def offTab : Nat → List (Array UInt8) → List UInt8
  | _, [] => []
  | s, p :: ps => (uintBytes 4 s).toList ++ offTab (s + p.size) ps

theorem headOf_toList : ∀ (ps : List (Array UInt8)) (s : Nat),
    (headOf s (offsetSlots ps)).toList = offTab s ps
  | [], _ => rfl
  | p :: ps, s => by
    simp only [offsetSlots_cons, headOf, bytesPerOffset, Array.toList_append, offTab, headOf_toList ps]

theorem bodiesOf_toList : ∀ (ps : List (Array UInt8)),
    (bodiesOf (offsetSlots ps)).toList = (ps.map Array.toList).flatten
  | [] => rfl
  | p :: ps => by simp only [offsetSlots_cons, bodiesOf, Array.toList_append, bodiesOf_toList ps]; simp

theorem offTab_length : ∀ (ps : List (Array UInt8)) (s : Nat), (offTab s ps).length = 4 * ps.length
  | [], _ => rfl
  | p :: ps, s => by simp [offTab, offTab_length ps, Fv.uintBytes_size]; omega

theorem offTab_get : ∀ (ps : List (Array UInt8)) (s j : Nat), j < ps.length →
    ((offTab s ps).drop (4 * j)).take 4 = (uintBytes 4 (s + ((ps.take j).map Array.size).sum)).toList
  | [], _, _, h => by simp at h
  | p :: ps, s, 0, _ => by simp [offTab, Fv.uintBytes_size]
  | p :: ps, s, j + 1, h => by
    have := offTab_get ps (s + p.size) j (by simp at h; omega)
    rw [show 4 * (j + 1) = 4 + 4 * j by omega, offTab, ← List.drop_drop,
      List.drop_left' (by simp [Fv.uintBytes_size])]
    rw [this]; simp [Nat.add_assoc]

theorem flatten_get : ∀ (Ls : List (List UInt8)) (i : Nat) (hi : i < Ls.length),
    (Ls.flatten.drop ((Ls.take i).map List.length).sum).take Ls[i].length = Ls[i]
  | [], _, h => by simp at h
  | L :: Ls, 0, _ => by simp
  | L :: Ls, i + 1, h => by
    have := flatten_get Ls i (by simp at h; omega)
    simp only [List.flatten_cons, List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    rw [← List.drop_drop, List.drop_left]; exact this

theorem lc_sizes (gs : List ListU64) (j : Nat) :
    (((gs.map luEncode).take j).map Array.size).sum = ((gs.take j).map fun g => 4 + 8 * g.l.length).sum := by
  rw [← List.map_take, List.map_map]
  congr 1; apply List.map_congr_left; intro g _; simp [lu_encode_size]

theorem lcBody_toList (g : ListCG) :
    (lcBody g).toList = offTab (4 * g.items.length) (g.items.map luEncode)
      ++ ((g.items.map luEncode).map Array.toList).flatten := by
  simp only [lcBody, lcParts, Array.toList_append, headOf_toList, bodiesOf_toList]

theorem lc_take_sizes (gs : List ListU64) (i : Nat) :
    (((gs.map luEncode).map Array.toList).take i |>.map List.length).sum
      = ((gs.take i).map fun g => 4 + 8 * g.l.length).sum := by
  rw [← lc_sizes, List.map_take, List.map_take, List.map_map, List.map_map]
  simp [Function.comp_def]

/-- The premises of `lc_accept_main` for the list bytes of an encoding. -/
theorem lc_tl_shape (g : ListCG) (hg : g.ok) :
    (lcBody g).toList.length = (lcBody g).size ∧ lcStart g.items g.items.length = (lcBody g).size
    ∧ (lcBody g).size < 2 ^ 32
    ∧ (1 ≤ g.items.length → (lcBody g).toList.take 4 = (uintBytes 4 (4 * g.items.length)).toList)
    ∧ (∀ i (hi : i < g.items.length), ((lcBody g).toList.drop (lcStart g.items i)).take (4 + 8 * g.items[i].l.length)
        = [4, 0, 0, 0] ++ (u64Bytes g.items[i].l).toList)
    ∧ (∀ i, i + 1 < g.items.length → ((lcBody g).toList.drop (4 * (i + 1))).take 4
        = (uintBytes 4 (lcStart g.items (i + 1))).toList) := by
  have hb := lcBody_size_le g hg
  have hL := lcBody_toList g
  have hoff := offTab_length (g.items.map luEncode) (4 * g.items.length)
  simp only [List.length_map] at hoff
  have hsz : (lcBody g).size = 4 * g.items.length + ((g.items.map luEncode).map Array.size).sum := by
    rw [← Array.length_toList, hL, List.length_append, hoff, List.length_flatten, List.map_map]
    congr 1
  have hall := lc_sizes g.items g.items.length
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)] at hall
  refine ⟨by simp, ?_, by omega, ?_, ?_, ?_⟩
  · simp only [lcStart, List.take_of_length_le (Nat.le_refl _)]; omega
  · intro h1
    rw [hL, List.take_append_of_le_length (by rw [hoff]; omega)]
    have := offTab_get (g.items.map luEncode) (4 * g.items.length) 0 (by simp; omega)
    simpa using this
  · intro i hi
    have hd : ∀ y, (offTab (4 * g.items.length) (g.items.map luEncode)
        ++ ((g.items.map luEncode).map Array.toList).flatten).drop (4 * g.items.length + y)
        = (((g.items.map luEncode).map Array.toList).flatten).drop y := by
      intro y; rw [show 4 * g.items.length + y = (offTab (4 * g.items.length) (g.items.map luEncode)).length + y by
        rw [hoff]]
      simp
    rw [hL, lcStart, hd, ← lc_take_sizes]
    have := flatten_get ((g.items.map luEncode).map Array.toList) i (by simp; omega)
    simp only [List.getElem_map, Array.length_toList, lu_encode_size] at this
    rw [this, luEncode_toList]
  · intro i hi
    rw [hL, List.drop_append_of_le_length (by rw [hoff]; omega), List.take_append_of_le_length (by simp [hoff]; omega)]
    rw [offTab_get _ _ (i + 1) (by simp; omega), lc_sizes]
    rfl

variable [Host]

set_option maxHeartbeats 4000000 in
/-- **ListC accept path against EthLib** (n ≥ 1, i.e. `len(buf) > 4`). If
EthLib accepts `bsA` as `v`, there is `g` with `g.toValue = v` and
`bsA = lcEncode g`; with the input chunks of that `g` the machine returns nil,
the receiver's Items header is (A, n, n), the items array holds n pointers,
and the objects (`lcObjs acc`) hold `g.items` in order. -/
theorem lc_unmarshal_accept_spec_k (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize lcDesc bsA = .ok v) (hne : 4 < bsA.size)
    (s : MachineData) (ra guard : UInt64) (fp slot s8 s32 l128 l136 l144 l152 l160 l168 l176 l184 l208 l216 l224 rslot blk
      cP cL cC : List UInt8)
    (hfp : fp.length = 8) (hsl : slot.length = 8) (h8 : s8.length = 8) (h32 : s32.length = 8)
    (hl128 : l128.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl152 : l152.length = 8)
    (hl160 : l160.length = 8) (hl168 : l168.length = 8) (hl176 : l176.length = 8) (hl184 : l184.length = 8)
    (hl208 : l208.length = 8) (hl216 : l216.length = 8) (hl224 : l224.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (S : Nat) (hS : S < 2 ^ 60) (hblk : blk.length = 144 + S)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 8 * 4 + 152 * 4 ≤ avail)
    (P : ∀ g : ListCG, bsA = lcEncode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s32.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (l144.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (l168.At (s.regs.rsp.toBitVec - 168))
      ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176)) ⋆ Eq (l184.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (l224.At (s.regs.rsp.toBitVec - 224)) ⋆ Eq (l216.At (s.regs.rsp.toBitVec - 216))
      ⋆ Eq (l208.At (s.regs.rsp.toBitVec - 208))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 232)) ⋆ Eq (blk.At (s.regs.rsp.toBitVec - 232 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq (((lcBody g).toList.take 4).At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq (((lcBody g).toList.drop 4).At (s.regs.rbx.toBitVec + 4 + 4))
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 400 + S < s.regs.rsp.toNat) (hsp : 400 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bsA.size) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hms : MakesliceC Heap (label "type__" + 114368).toBitVec 8 (144 + S))
    (hno : NewobjectC Heap (label "type__" + 83104).toBitVec 24 (144 + S)) (hlu : LuUAccC Heap S) :
    ∃ g : ListCG, g.toValue = v ∧ bsA = lcEncode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧
        ∃ (A : BitVec 64) (acc : List (BitVec 64 × BitVec 64 × ListU64)) (avail' : Nat),
          acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.2.2) = g.items ∧
          (Eq ((Int.toBytes 8 A.toInt).At s.regs.rax.toBitVec)
            ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 g.items.length).toInt).At (s.regs.rax.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 g.items.length).toInt).At (s.regs.rax.toBitVec + 16))
            ⋆ Eq ((ptrBytes (acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))).At A)
            ⋆ lcObjs acc ⋆ Eq ((lcBody g).toList.At (s.regs.rbx.toBitVec + 4)) ⋆ Heap avail' ⋆ fun _ => True)
            st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, hg, rfl, rfl⟩ := lc_accepted bsA v hd
  refine ⟨g, rfl, rfl, ?_⟩
  obtain ⟨hT, hend, hT32, hfirst, hparts, hnexts⟩ := lc_tl_shape g hg
  have hsz : (lcEncode g).size = 4 + (lcBody g).size := by simp [lcEncode, Fv.uintBytes_size]
  have hn1 : 1 ≤ g.items.length := by
    rcases Nat.eq_zero_or_pos g.items.length with h | h
    · exfalso; rw [List.length_eq_zero_iff] at h
      have := (lc_shape g hg).2.2.1 h; omega
    · exact h
  exact lc_accept_main k hk hf (lcBody g).toList (lcBody g).size g.items hg.2 hT hn1 hg.1 hT32 hend (hfirst hn1)
    hparts hnexts s ra guard fp slot s8 s32 l128 l136 l144 l152 l160 l168 l176 l184 l208 l216 l224 rslot blk cP cL cC
    hfp hsl h8 h32 hl128 hl136 hl144 hl152 hl160 hl168 hl176 hl184 hl208 hl216 hl224 hrs hcP hcL hcC S hS hblk
    R Heap avail hav (P g rfl) hguard hsp (by rw [hlen, hsz]) hcap hcap63 hms hno hlu
