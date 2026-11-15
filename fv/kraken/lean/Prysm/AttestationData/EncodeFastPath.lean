import Prysm.AttestationData.EncodeHead
import Prysm.AttestationData.EncodeCalls

/-!
# Real Prysm `(*v1alpha1.AttestationData).MarshalSSZTo`, fast path, Go 1.26.10 machine code

    func (a *AttestationData) MarshalSSZTo(dst []byte) ([]byte, error) {
        dst = ssz.MarshalUint64(dst, uint64(a.Slot))             // inlined
        dst = ssz.MarshalUint64(dst, uint64(a.CommitteeIndex))   // inlined
        if len(a.BeaconBlockRoot) != 32 { return nil, ssz.ErrBytesLength }
        dst = append(dst, a.BeaconBlockRoot...)                  // runtime.memmove
        if a.Source == nil { a.Source = new(Checkpoint) }
        if dst, err = a.Source.MarshalSSZTo(dst); err != nil { ... }
        if a.Target == nil { a.Target = new(Checkpoint) }
        if dst, err = a.Target.MarshalSSZTo(dst); err != nil { ... }
        return dst, nil }

`Encode.fast_path` composes `Encode.head` (directives 0–90) and `Encode.calls` (90 to the return).
On the fast path every stack check passes and every capacity test finds room.
Also `len(BeaconBlockRoot) = 32`, and `Source` and `Target` are not nil.
Each Checkpoint has `len(Root) = 32`, so each Checkpoint call takes its fast path.
`runtime.memmove` is used through `MemmoveContract S`.
`Checkpoint.MarshalSSZTo` is used twice through `Prysm.Checkpoint.Encode.fast_path_function_spec_holds`.
Its code is at index `kC`.
The stack below the return slot rsp − 192 is one block.
The block has `S + 120` bytes at rsp − 312 − S.
The memmove call uses the top `S` bytes of the block as its scratch.
Each Checkpoint call uses the block as scratch (S), return slot and an untouched 48-byte gap.
It also uses the block for two temp halves and four words.

Limits of the statement:
- The separating conjunction of the premise makes the memory blocks disjoint.
- These blocks are the receiver, `dst`, the root, the two Checkpoint structs and their two roots.
- So `Source = Target` is not covered.
- Two roots in one shared backing array are not covered either.
- Go allows both.
- Other premises: `Source` and `Target` are not nil, and `cap < 2^63`.
- The stack bound is `guard + 312 < rsp`, for the stack checks of both callees.
- Paths not proved: the three growslice sites and the root length reject.
- Also not proved: the `newobject` branches for a nil `Source` or `Target`.
- Also not proved: the error wraps of the two callee calls, and morestack.
-/

open Machine Runtime Prysm.AttestationData.Code

namespace Prysm.AttestationData

/-- The block below the return slot, as the memmove view: 120 low bytes and the `S` scratch bytes of memmove. -/
theorem Encode.low_memmove_view (x : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (lo : List UInt8) (h : lo.length = S + 120) :
    Eq (lo.At (x - 312 - BitVec.ofNat 64 S)) =
      Eq ((lo.take 120).At (x - 312 - BitVec.ofNat 64 S)) ⋆ Eq ((lo.drop 120).At (x - 192 - BitVec.ofNat 64 S)) := by
  conv => lhs; rw [← List.take_append_drop 120 lo]
  exact at_app _ _ (by rw [List.length_take, h, Nat.min_eq_left (by omega)]; bv_omega)
    (by rw [List.length_take, List.length_drop, h]; omega)

/-- The `S + 120` bytes below the return slot of a Checkpoint call.
They are the slots of the Checkpoint encoder's frame.
The order is scratch (S), return slot, gap (48), t40 (16), t30 (16), l32, l24, l16 and fp. -/
def Encode.calleeFrame (scratch rs gap t40 t30 l32 l24 l16 fp : List UInt8) : List UInt8 :=
  scratch ++ (rs ++ (gap ++ (t40 ++ (t30 ++ (l32 ++ (l24 ++ (l16 ++ fp)))))))

/-- The callee frame block as its nine parts. -/
theorem Encode.calleeFrame_sep (x : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (scratch rs gap t40 t30 l32 l24 l16 fp : List UInt8)
    (h0 : scratch.length = S) (h1 : rs.length = 8) (h2 : gap.length = 48) (h3 : t40.length = 16)
    (h4 : t30.length = 16) (h5 : l32.length = 8) (h6 : l24.length = 8) (h7 : l16.length = 8) (h8 : fp.length = 8) :
    Eq ((Encode.calleeFrame scratch rs gap t40 t30 l32 l24 l16 fp).At (x - 312 - BitVec.ofNat 64 S)) =
      Eq (scratch.At (x - 312 - BitVec.ofNat 64 S)) ⋆ Eq (rs.At (x - 312)) ⋆ Eq (gap.At (x - 304))
      ⋆ Eq (t40.At (x - 256)) ⋆ Eq (t30.At (x - 240)) ⋆ Eq (l32.At (x - 224)) ⋆ Eq (l24.At (x - 216))
      ⋆ Eq (l16.At (x - 208)) ⋆ Eq (fp.At (x - 200)) := by
  simp only [Encode.calleeFrame]
  rw [at_app _ _ (b := x - 312) (by rw [h0]; bv_omega) (by simp [*]; omega),
    at_app _ _ (b := x - 304) (by rw [h1]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 256) (by rw [h2]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 240) (by rw [h3]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 224) (by rw [h4]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 216) (by rw [h5]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 208) (by rw [h6]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 200) (by rw [h7]; bv_omega) (by simp [*])]
  simp only [Std.ExtHashMap.sep_assoc]

/-- Any block of `S + 120` bytes is an `Encode.calleeFrame` (slices by nested `drop`). -/
theorem Encode.calleeFrame_slices (L : List UInt8) (S : Nat) :
    let t0 := L.drop S; let t1 := t0.drop 8; let t2 := t1.drop 48; let t3 := t2.drop 16
    let t4 := t3.drop 16; let t5 := t4.drop 8; let t6 := t5.drop 8; let t7 := t6.drop 8
    L = Encode.calleeFrame (L.take S) (t0.take 8) (t1.take 48) (t2.take 16) (t3.take 16) (t4.take 8) (t5.take 8)
      (t6.take 8) t7 := by
  intro t0 t1 t2 t3 t4 t5 t6 t7
  simp only [Encode.calleeFrame, t0, t1, t2, t3, t4, t5, t6, t7, List.take_append_drop]

/-- The lengths of the slices of `Encode.calleeFrame_slices`. -/
theorem Encode.calleeFrame_lengths (L : List UInt8) (S : Nat) (h : L.length = S + 120) :
    (L.take S).length = S ∧ ((L.drop S).take 8).length = 8 ∧ (((L.drop S).drop 8).take 48).length = 48
      ∧ ((((L.drop S).drop 8).drop 48).take 16).length = 16
      ∧ (((((L.drop S).drop 8).drop 48).drop 16).take 16).length = 16
      ∧ ((((((L.drop S).drop 8).drop 48).drop 16).drop 16).take 8).length = 8
      ∧ (((((((L.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).take 8).length = 8
      ∧ ((((((((L.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).drop 8).take 8).length = 8
      ∧ ((((((((L.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).drop 8).drop 8).length = 8 := by
  simp only [List.length_take, List.length_drop, h]; omega

/-- The prefix of the Source call: the caller's prefix and the 48 head bytes. -/
theorem Encode.merge_head_prefix (pre a b c : List UInt8) (d n : BitVec 64) (hpre : pre.length = n.toNat)
    (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 32) (hn : n.toNat + 48 < 2 ^ 64) :
    Eq ((pre ++ a ++ b ++ c).At d) =
      Eq (pre.At d) ⋆ Eq (a.At (d + n)) ⋆ Eq (b.At (d + n + 8)) ⋆ Eq (c.At (d + n + 16)) := by
  simp only [List.append_assoc]
  rw [at_app pre _ (b := d + n) (by rw [hpre]; simp) (by simp only [List.length_append, hpre, ha, hb, hc]; omega),
    at_app a _ (b := d + n + 8) (by rw [ha]; rfl) (by simp only [List.length_append, ha, hb, hc]; omega),
    at_app b c (b := d + n + 16) (by rw [hb]; bv_omega) (by simp only [hb, hc]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The 128 encoder bytes at `dst[len:]` as their seven fields. -/
theorem Encode.merge_encoding (a b c e f g h : List UInt8) (p : BitVec 64)
    (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 32) (he : e.length = 8) (hf : f.length = 32)
    (hg : g.length = 8) (hh : h.length = 32) :
    Eq ((a ++ b ++ c ++ e ++ f ++ g ++ h).At p) =
      Eq (a.At p) ⋆ Eq (b.At (p + 8)) ⋆ Eq (c.At (p + 16)) ⋆ Eq (e.At (p + 48)) ⋆ Eq (f.At (p + 56))
      ⋆ Eq (g.At (p + 88)) ⋆ Eq (h.At (p + 96)) := by
  simp only [List.append_assoc]
  rw [at_app a _ (b := p + 8) (by rw [ha]; rfl) (by simp only [List.length_append, *]; omega),
    at_app b _ (b := p + 16) (by rw [hb]; bv_omega) (by simp only [List.length_append, *]; omega),
    at_app c _ (b := p + 48) (by rw [hc]; bv_omega) (by simp only [List.length_append, *]; omega),
    at_app e _ (b := p + 56) (by rw [he]; bv_omega) (by simp only [List.length_append, *]; omega),
    at_app f _ (b := p + 88) (by rw [hf]; bv_omega) (by simp only [List.length_append, *]; omega),
    at_app g h (b := p + 96) (by rw [hg]; bv_omega) (by simp only [*]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The `dst` addresses of the Checkpoint calls, from `len + 48`. -/
theorem Encode.dst_addresses (d n : BitVec 64) :
    d + (n + 48) = d + n + 48 ∧ d + (n + 48) + 8 = d + n + 56 ∧ d + (n + 48) + 40 = d + n + 88
      ∧ d + (n + 48) + 48 = d + n + 96 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

variable [Host]

/-- **Encoder fast path of `(*v1alpha1.AttestationData).MarshalSSZTo`.**
The code at index `k` writes 128 bytes at `dst[len:len+128]`.
They are the Slot bytes, the CommitteeIndex bytes and the 32 root bytes.
Then come the 40 encoder bytes of Source and the 40 encoder bytes of Target.
The function returns `(dst.ptr, len + 128, cap, nil)`.
The receiver, both Checkpoints and the prefix stay unchanged.
The post-state names every frame slot that the path writes and the slots that the callee theorems name. -/
theorem Encode.fast_path (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.marshalSSZTo.IsInfixAt Host.prog kC)
    (hfC : LabelsFresh Prysm.Checkpoint.Code.marshalSSZTo kC)
    (S : Nat) (hS : S < 2 ^ 60) (hmm : MemmoveContract S)
    (s : MachineData) (ra guard : UInt64) (rp ps pt p1 p2 : BitVec 64) (hps : ps ≠ 0) (hpt : pt ≠ 0)
    (sl ix root cs e1 cC1 ctl1 root1 ct e2 cC2 ctl2 root2 pre d0 d1 d2 d3 d4 d5 d6 : List UInt8)
    (hsl : sl.length = 8) (hix : ix.length = 8) (hroot : root.length = 32)
    (hcs : cs.length = 8) (he1 : e1.length = 8) (hcC1 : cC1.length = 8) (hctl1 : ctl1.length = 32)
    (hroot1 : root1.length = 32)
    (hct : ct.length = 8) (he2 : e2.length = 8) (hcC2 : cC2.length = 8) (hctl2 : ctl2.length = 32)
    (hroot2 : root2.length = 32)
    (hpre : pre.length = s.regs.rcx.toNat) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (hd3 : d3.length = 8) (hd4 : d4.length = 32) (hd5 : d5.length = 8) (hd6 : d6.length = 32)
    (fp a8 b16 ta tb tc td q48 q120 q128 q176 rslot lo : List UInt8)
    (hfp : fp.length = 8) (ha8 : a8.length = 8) (hb16 : b16.length = 8) (hta : ta.length = 16) (htb : tb.length = 16)
    (htc : tc.length = 16) (htd : td.length = 16) (h48 : q48.length = 8) (h120 : q120.length = 8)
    (h128 : q128.length = 8) (h176 : q176.length = 8) (hrs : rslot.length = 8) (hlo : lo.length = S + 120)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (a8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (b16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (ta.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (tb.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (tc.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (td.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (q48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (q120.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (q128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (q176.At (s.regs.rsp.toBitVec - 176))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (ix.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 rp.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 pt.toInt).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (root.At rp)
      ⋆ Eq (cs.At ps) ⋆ Eq (e1.At (ps + 8)) ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (ps + 24)) ⋆ Eq (cC1.At (ps + 32)) ⋆ Eq (ctl1.At (ps + 40)) ⋆ Eq (root1.At p1)
      ⋆ Eq (ct.At pt) ⋆ Eq (e2.At (pt + 8)) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (pt + 24)) ⋆ Eq (cC2.At (pt + 32)) ⋆ Eq (ctl2.At (pt + 40)) ⋆ Eq (root2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
      ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ Eq (d6.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96)) ⋆ R)
    (hguard : guard.toNat + 312 < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 128 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 128 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t1 u1 t2 u2 t u scr rs' gap : List UInt8), t1.length = 8 ∧ u1.length = 16 ∧ t2.length = 8
          ∧ u2.length = 16 ∧ t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧ rs'.length = 8 ∧ gap.length = 48 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (t1.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (u1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (ix.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (t2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (u2.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 178)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rsp.toBitVec - 8).toInt).At (s.regs.rsp.toBitVec - 200))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 208))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 216))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48 + 40 + 40).toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 240)) ⋆ Eq (e2.At (s.regs.rsp.toBitVec - 256))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 248)) ⋆ Eq (gap.At (s.regs.rsp.toBitVec - 304))
          ⋆ Eq (rs'.At (s.regs.rsp.toBitVec - 312)) ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (ix.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 rp.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 pt.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (root.At rp)
          ⋆ Eq (cs.At ps) ⋆ Eq (e1.At (ps + 8)) ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 24)) ⋆ Eq (cC1.At (ps + 32)) ⋆ Eq (ctl1.At (ps + 40)) ⋆ Eq (root1.At p1)
          ⋆ Eq (ct.At pt) ⋆ Eq (e2.At (pt + 8)) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 24)) ⋆ Eq (cC2.At (pt + 32)) ⋆ Eq (ctl2.At (pt + 40)) ⋆ Eq (root2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq ((sl ++ ix ++ root ++ e1 ++ root1 ++ e2 ++ root2).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hcp := Prysm.Checkpoint.Encode.fast_path_function_spec_holds kC hkC hfC S hmm
  have := s.regs.rcx.toNat_lt_size; have := s.regs.rdi.toNat_lt_size
  simp only [UInt64.size] at *
  rw [Encode.low_memmove_view _ S hS lo hlo] at h_mem
  refine eventually_trans _ _ _ _ (Encode.head k hk hf s ra guard rp sl ix root d0 d1 d2 hsl hix hroot hd0 hd1 hd2
    fp a8 b16 ta tb tc td q48 q120 q128 rslot hfp ha8 hb16 hta htb htc htd h48 h120 h128 hrs S (lo.drop 120)
    (by rw [List.length_drop, hlo]; omega)
    (Eq ((lo.take 120).At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
      ⋆ Eq (q176.At (s.regs.rsp.toBitVec - 176))
      ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 pt.toInt).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (cs.At ps) ⋆ Eq (e1.At (ps + 8)) ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (ps + 24)) ⋆ Eq (cC1.At (ps + 32)) ⋆ Eq (ctl1.At (ps + 40)) ⋆ Eq (root1.At p1)
      ⋆ Eq (ct.At pt) ⋆ Eq (e2.At (pt + 8)) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (pt + 24)) ⋆ Eq (cC2.At (pt + 32)) ⋆ Eq (ctl2.At (pt + 40)) ⋆ Eq (root2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
      ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ Eq (d6.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96)) ⋆ R)
    (cast (congrFun (by ac_rfl) _) h_mem) (by omega) (by omega) hcap63 hmm) ?_
  rintro ⟨st, pc⟩ ⟨hpc, hrsp1, hrbp1, hr141, t1, u1, t2, u2, scr0, ht1, hu1, ht2, hu2, hscr0, Hm⟩
  dsimp only at hpc hrsp1 hrbp1 hr141 Hm
  subst hpc
  have hn48 : (s.regs.rcx.toBitVec + 48).toNat = s.regs.rcx.toNat + 48 := by
    rw [BitVec.toNat_add, UInt64.toNat_toBitVec, show (48 : BitVec 64).toNat = 48 from rfl]; omega
  -- The block below the return slot, after memmove, as the Checkpoint callee frame.
  have hL : (lo.take 120 ++ scr0).length = S + 120 := by
    rw [List.length_append, List.length_take, hlo, hscr0]; omega
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := Encode.calleeFrame_lengths _ S hL
  have Hm' : (Eq ((lo.take 120 ++ scr0).At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S)) ⋆ ?F) st.dmem := by
    rw [at_app (lo.take 120) scr0 (b := s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S)
      (by rw [List.length_take, hlo, Nat.min_eq_left (by omega)]; bv_omega) (by rw [← List.length_append, hL]; omega)]
    ecancel
  clear Hm
  rw [Encode.calleeFrame_slices (lo.take 120 ++ scr0) S] at Hm'
  try dsimp only at Hm'
  rw [Encode.calleeFrame_sep _ S hS _ _ _ _ _ _ _ _ _ l0 l1 l2 l3 l4 l5 l6 l7 l8] at Hm'
  have hpre' : (pre ++ sl ++ ix ++ root).length = (s.regs.rcx.toBitVec + 48).toNat := by
    simp only [List.length_append, hpre, hsl, hix, hroot, hn48]
  obtain ⟨a1, a2, a3, a4⟩ := Encode.dst_addresses s.regs.rbx.toBitVec s.regs.rcx.toBitVec
  refine eventually_mono (Encode.calls k hk hf S hcp s.regs.rsp.toBitVec s.regs.rax.toBitVec ps pt p1 p2
    s.regs.rbx.toBitVec (s.regs.rcx.toBitVec + 48) s.regs.rdi.toBitVec hps hpt ra s.regs.rbp guard st
    cs e1 cC1 ctl1 root1 ct e2 cC2 ctl2 root2 (pre ++ sl ++ ix ++ root) d3 d4 d5 d6
    (Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt) _ q176 _ _ _ _ _ _ _
    hcs he1 hcC1 hctl1 hroot1 hct he2 hcC2 hctl2 hroot2 hpre' hd3 hd4 hd5 hd6 (Int.toBytes_length 8 _)
    l8 h176 l7 l6 l5 l3 l4 l1 l0 hrsp1 _
    (by
      rw [Encode.merge_head_prefix pre sl ix root _ _ hpre hsl hix hroot (by rw [UInt64.toNat_toBitVec]; omega),
        a2, a3, a4, a1, hr141]
      ecancel)
    hguard (by rw [hn48, UInt64.toNat_toBitVec]; omega) hcap63) ?_
  rintro st' ⟨hpc2, hrax2, hrbx2, hrcx2, hrdi2, hrsi2, hrsp2, hrbp2, hr142, t, u, scr, rs', ht, hu, hscr, hrs', Hm2⟩
  refine ⟨hpc2, UInt64.toBitVec_inj.mp hrax2, by rw [hrbx2, hn48], UInt64.toBitVec_inj.mp hrcx2, hrdi2, hrsi2,
    by rw [hrsp2]; apply UInt64.toBitVec_inj.mp; simp, hrbp2, by rw [hr142, hr141],
    t1, u1, t2, u2, t, u, scr, rs', _, ht1, hu1, ht2, hu2, ht, hu, hscr, hrs', l2, ?_⟩
  rw [Encode.merge_head_prefix pre sl ix root _ _ hpre hsl hix hroot (by rw [UInt64.toNat_toBitVec]; omega),
    a2, a3, a4, a1, hrbp1, hr141] at Hm2
  rw [Encode.merge_encoding sl ix root e1 root1 e2 root2 _ hsl hix hroot he1 hroot1 he2 hroot2]
  dsimp only at Hm2
  exact cast (congrFun (by ac_rfl) _) Hm2

end Prysm.AttestationData
