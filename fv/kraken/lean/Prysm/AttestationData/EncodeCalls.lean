module

public import Prysm.AttestationData.EncodeTargetCall

@[expose] public section

/-!
# `(*v1alpha1.AttestationData).MarshalSSZTo`, fast path, segments 4 and 5 together

`Encode.calls` composes `Encode.source_call` (directives 90–147) and `Encode.target_call` (147 to the return).
The Target call gets the frame that the Source call leaves.
That frame is the return slot, the callee frame words and the scratch.
The prefix of the Target call is the prefix of the Source call and the 40 Source bytes.
-/

open Machine Runtime Prysm.AttestationData.Code

namespace Prysm.AttestationData

/-- A prefix and two appended fields as one list. -/
theorem Encode.merge_prefix (pre a b : List UInt8) (d m : BitVec 64) (hpre : pre.length = m.toNat) (ha : a.length = 8)
    (hb : b.length = 32) (hm : m.toNat + 40 < 2 ^ 64) :
    Eq ((pre ++ a ++ b).At d) = Eq (pre.At d) ⋆ Eq (a.At (d + m)) ⋆ Eq (b.At (d + m + 8)) := by
  rw [List.append_assoc, at_app pre (a ++ b) (b := d + m) (by rw [hpre]; simp)
      (by simp only [List.length_append, hpre, ha, hb]; omega),
    at_app a b (b := d + m + 8) (by rw [ha]; rfl) (by simp only [ha, hb]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The 16-byte callee temp as its two words. -/
theorem Encode.merge_temp (e t : List UInt8) (x : BitVec 64) (he : e.length = 8) (ht : t.length = 8) :
    Eq ((e ++ t).At (x - 256)) = Eq (e.At (x - 256)) ⋆ Eq (t.At (x - 248)) :=
  at_app e t (by rw [he]; bv_omega) (by rw [he, ht]; omega)

/-- The length register after the Source call, as a bit vector. -/
theorem Encode.length_after_source (r : UInt64) (m cap : BitVec 64) (h : r.toNat = m.toNat + 40)
    (hcap : m.toNat + 80 ≤ cap.toNat) : r.toBitVec = m + 40 := by
  apply BitVec.eq_of_toNat_eq
  have := cap.isLt
  have h40 : (40 : BitVec 64).toNat = 40 := rfl
  rw [UInt64.toNat_toBitVec, h, BitVec.toNat_add, h40]
  omega

variable [Host]

/-- Segments 4 and 5 of the encoder fast path: from directive 90 to the return, through both Checkpoint encoders. -/
theorem Encode.calls (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (S : Nat) (hcp : Prysm.Checkpoint.Encode.fast_path_function_spec S)
    (x rcv ps pt p1 p2 d m cap : BitVec 64) (hps : ps ≠ 0) (hpt : pt ≠ 0) (ra rb0 guard : UInt64) (s : MachineData)
    (cs e1 cC1 ctl1 root1 ct e2 cC2 ctl2 root2 pre d3 d4 d5 d6 : List UInt8)
    (rslot fp s2 l16 l24 l32 t40 t30 rs scratch : List UInt8)
    (hcs : cs.length = 8) (he1 : e1.length = 8) (hcC1 : cC1.length = 8) (hctl1 : ctl1.length = 32)
    (hroot1 : root1.length = 32)
    (hct : ct.length = 8) (he2 : e2.length = 8) (hcC2 : cC2.length = 8) (hctl2 : ctl2.length = 32)
    (hroot2 : root2.length = 32)
    (hpre : pre.length = m.toNat) (hd3 : d3.length = 8) (hd4 : d4.length = 32) (hd5 : d5.length = 8)
    (hd6 : d6.length = 32)
    (hrslot : rslot.length = 8) (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16)
    (hrs : rs.length = 8) (hsc : scratch.length = S)
    (hrsp : s.regs.rsp = { toBitVec := x - 184 })
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rb0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At (x + 8))
      ⋆ Eq ((Int.toBytes 8 ps.toInt).At (rcv + 48)) ⋆ Eq ((Int.toBytes 8 pt.toInt).At (rcv + 56))
      ⋆ Eq ((Int.toBytes 8 d.toInt).At (x - 48)) ⋆ Eq ((Int.toBytes 8 m.toInt).At (x - 120))
      ⋆ Eq ((Int.toBytes 8 cap.toInt).At (x - 128))
      ⋆ Eq (rslot.At (x - 192)) ⋆ Eq (fp.At (x - 200)) ⋆ Eq (s2.At (x - 176))
      ⋆ Eq (l16.At (x - 208)) ⋆ Eq (l24.At (x - 216)) ⋆ Eq (l32.At (x - 224)) ⋆ Eq (t30.At (x - 240))
      ⋆ Eq (t40.At (x - 256)) ⋆ Eq (rs.At (x - 312)) ⋆ Eq (scratch.At (x - 312 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cs.At ps) ⋆ Eq (e1.At (ps + 8)) ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (ps + 24)) ⋆ Eq (cC1.At (ps + 32)) ⋆ Eq (ctl1.At (ps + 40)) ⋆ Eq (root1.At p1)
      ⋆ Eq (ct.At pt) ⋆ Eq (e2.At (pt + 8)) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (pt + 24)) ⋆ Eq (cC2.At (pt + 32)) ⋆ Eq (ctl2.At (pt + 40)) ⋆ Eq (root2.At p2)
      ⋆ Eq (pre.At d) ⋆ Eq (d3.At (d + m)) ⋆ Eq (d4.At (d + m + 8)) ⋆ Eq (d5.At (d + m + 40))
      ⋆ Eq (d6.At (d + m + 48)) ⋆ R)
    (hguard : guard.toNat + 312 < x.toNat)
    (hcap : m.toNat + 80 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toBitVec = d
        ∧ st.data.regs.rbx.toNat = m.toNat + 80 ∧ st.data.regs.rcx.toBitVec = cap
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = { toBitVec := x + 8 } ∧ st.data.regs.rbp = rb0 ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u scr rs' : List UInt8), t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧ rs'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rb0.toBitVec.toInt).At (x - 8))
          ⋆ Eq ((Int.toBytes 8 rcv.toInt).At (x + 8))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (rcv + 48)) ⋆ Eq ((Int.toBytes 8 pt.toInt).At (rcv + 56))
          ⋆ Eq ((Int.toBytes 8 d.toInt).At (x - 48)) ⋆ Eq ((Int.toBytes 8 m.toInt).At (x - 120))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (x - 128))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 178)).toBitVec.toInt).At (x - 192))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (x - 200))
          ⋆ Eq ((Int.toBytes 8 d.toInt).At (x - 176))
          ⋆ Eq ((Int.toBytes 8 d.toInt).At (x - 208)) ⋆ Eq ((Int.toBytes 8 cap.toInt).At (x - 216))
          ⋆ Eq ((Int.toBytes 8 (m + 40 + 40).toInt).At (x - 224)) ⋆ Eq (u.At (x - 240))
          ⋆ Eq (e2.At (x - 256)) ⋆ Eq (t.At (x - 248))
          ⋆ Eq (rs'.At (x - 312)) ⋆ Eq (scr.At (x - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cs.At ps) ⋆ Eq (e1.At (ps + 8)) ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 24)) ⋆ Eq (cC1.At (ps + 32)) ⋆ Eq (ctl1.At (ps + 40)) ⋆ Eq (root1.At p1)
          ⋆ Eq (ct.At pt) ⋆ Eq (e2.At (pt + 8)) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 24)) ⋆ Eq (cC2.At (pt + 32)) ⋆ Eq (ctl2.At (pt + 40)) ⋆ Eq (root2.At p2)
          ⋆ Eq (pre.At d) ⋆ Eq (e1.At (d + m)) ⋆ Eq (root1.At (d + m + 8)) ⋆ Eq (e2.At (d + m + 40))
          ⋆ Eq (root2.At (d + m + 48)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 90)⟩ := by
  have := m.isLt; have := cap.isLt
  refine eventually_trans _ _ _ _ (Encode.source_call k hk hf S hcp x rcv ps p1 d m cap hps guard s
    cs e1 cC1 ctl1 root1 pre d3 d4 rslot fp s2 l16 l24 l32 t40 t30 rs scratch hcs he1 hcC1 hctl1 hroot1 hpre hd3 hd4
    hrslot hfp h2 hl16 hl24 hl32 ht40 ht30 hrs hsc hrsp
    (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rb0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 pt.toInt).At (rcv + 56))
      ⋆ Eq (ct.At pt) ⋆ Eq (e2.At (pt + 8)) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (pt + 24)) ⋆ Eq (cC2.At (pt + 32)) ⋆ Eq (ctl2.At (pt + 40)) ⋆ Eq (root2.At p2)
      ⋆ Eq (d5.At (d + m + 40)) ⋆ Eq (d6.At (d + m + 48)) ⋆ R)
    (cast (congrFun (by ac_rfl) _) h_mem) hguard (by omega) hcap63) ?_
  rintro ⟨st, pc⟩ ⟨hpc, hrax, hrbx, hrcx, hrsp', hrbp', hr14', t, u, scr, rs', ht, hu, hscr, hrs', Hm⟩
  dsimp only at hpc hrax hrbx hrcx hrsp' hrbp' hr14' Hm
  subst hpc
  have hrb : st.regs.rbx.toBitVec = m + 40 := Encode.length_after_source _ m cap hrbx hcap
  have hpre' : (pre ++ e1 ++ root1).length = st.regs.rbx.toNat := by
    simp only [List.length_append, hpre, he1, hroot1, hrbx]
  refine eventually_mono (Encode.target_call k hk hf S hcp x rcv pt p2 d cap hpt ra rb0 guard st
    ct e2 cC2 ctl2 root2 (pre ++ e1 ++ root1) d5 d6
    (Int.toBytes 8 (Host.addrOf (k + 113)).toBitVec.toInt) (Int.toBytes 8 s.regs.rbp.toBitVec.toInt)
    (Int.toBytes 8 d.toInt) (Int.toBytes 8 d.toInt) (Int.toBytes 8 cap.toInt) (Int.toBytes 8 (m + 40).toInt)
    (e1 ++ t) u rs' scr hct he2 hcC2 hctl2 hroot2 hpre' hd5 hd6
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (by simp only [List.length_append, he1, ht]) hu hrs' hscr
    (by rw [hrsp', hrsp]) hrax hrcx
    (Eq ((Int.toBytes 8 ps.toInt).At (rcv + 48))
      ⋆ Eq ((Int.toBytes 8 d.toInt).At (x - 48)) ⋆ Eq ((Int.toBytes 8 m.toInt).At (x - 120))
      ⋆ Eq ((Int.toBytes 8 cap.toInt).At (x - 128))
      ⋆ Eq (cs.At ps) ⋆ Eq (e1.At (ps + 8)) ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (ps + 24)) ⋆ Eq (cC1.At (ps + 32)) ⋆ Eq (ctl1.At (ps + 40)) ⋆ Eq (root1.At p1) ⋆ R)
    (by
      rw [hrb, Encode.merge_prefix pre e1 root1 d m hpre he1 hroot1 (by omega), Encode.merge_temp e1 t x he1 ht,
        show x + 0 = x from BitVec.add_zero x, show d + (m + 40) = d + m + 40 by rw [BitVec.add_assoc], hr14']
      exact cast (congrFun (by ac_rfl) _) Hm)
    hguard (by rw [hrbx]; omega) hcap63) ?_
  rintro st' ⟨hpc2, hrax2, hrbx2, hrcx2, hrdi2, hrsi2, hrsp2, hrbp2, hr142, t2, u2, scr2, rs2, ht2, hu2, hscr2, hrs2, Hm2⟩
  refine ⟨hpc2, hrax2, by rw [hrbx2, hrbx], hrcx2, hrdi2, hrsi2, hrsp2, hrbp2, by rw [hr142, hr14'],
    t2, u2, scr2, rs2, ht2, hu2, hscr2, hrs2, ?_⟩
  rw [hrb, Encode.merge_prefix pre e1 root1 d m hpre he1 hroot1 (by omega), show x + 0 = x from BitVec.add_zero x,
    show d + (m + 40) = d + m + 40 by rw [BitVec.add_assoc],
    show d + m + 40 + 8 = d + m + 48 by rw [BitVec.add_assoc]; rfl, hrbp', hr14'] at Hm2
  exact cast (congrFun (by ac_rfl) _) Hm2

end Prysm.AttestationData
