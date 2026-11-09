"""Template text of the ListC accept proofs (X4), used by lcacc.py.

Copied from the hand proofs Fk/LcLoop.lean (lcl_iter statement, lcl_exit statement, lcl_loop),
Fk/LcAccept.lean (lc_accept_main statement, proof head, loop call, finish) and Fk/LcAcceptEmpty.lean
(statement, finish), and the makeslice call block ACC_MS of Fk/LcAccept.lean. Replaced by placeholders: the code name @CODE@, the loop head @HEAD@ and exit @EXIT@
labels, the newobject @NOTY@ and makeslice @MSTY@ type words and the makeslice call site @MSCALL@;
lcacc.py reads them from UnmarshalSSZ.S. Everything else (frame offsets, value names, tactic text)
is hand text; lcacc.py refuses code whose frame layout differs from the one this text assumes.
"""

ITER_STMT = '''theorem lcl_iter [Host] (k : Nat) (hk : @CODE@.IsInfixAt Host.prog k)
    (hf : LabelsFresh @CODE@ k)
    (x base recv A : BitVec 64) (tl ptrs : List UInt8) (T n i s e : Nat) (g : ListU64) (hg : g.ok)
    (hT : tl.length = T) (hn : n ≤ 4) (hi : i < n) (hptrs : ptrs.length = 8 * i)
    (hse : s + (4 + 8 * g.l.length) = e) (heT : e ≤ T) (hs4 : 4 * n ≤ s)
    (hpart : (tl.drop s).take (4 + 8 * g.l.length) = [4, 0, 0, 0] ++ (u64Bytes g.l).toList)
    (hnext : i + 1 < n → (tl.drop (4 * (i + 1))).take 4 = (uintBytes 4 e).toList)
    (hlast : i + 1 = n → e = T)
    (hT32 : T < 2 ^ 32) (cap0 : Nat) (hcap : T + 4 ≤ cap0) (hcap63 : cap0 < 2 ^ 63)
    (S : Nat) (hS : S < 2 ^ 60) (blk rslot sp1 sp2 s136 s152 s160 s184 : List UInt8)
    (hblk : blk.length = 144 + S) (hrs : rslot.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (h136 : s136.length = 8) (h152 : s152.length = 8) (h160 : s160.length = 8) (h184 : s184.length = 8)
    (ra rbp0 guard : UInt64) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 24 + 8 * 16 ≤ avail)
    (O R : DataMem → Prop) (s0 : MachineData)
    (hrax : s0.regs.rax.toNat = i) (hrdx : s0.regs.rdx.toNat = n) (hrcx : s0.regs.rcx.toNat = s)
    (hrsp : s0.regs.rsp.toBitVec = x - 8#64 - 216)
    (hguard : guard.toNat + 400 + S < x.toNat) (hx : 400 + S ≤ x.toNat)
    (h_mem : s0.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 recv.toInt).At (x + 8))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt).At (x + 32))
      ⋆ Eq ((Int.toBytes 8 base.toInt).At (x - 128)) ⋆ Eq (s136.At (x - 136))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt).At (x - 144))
      ⋆ Eq (s152.At (x - 152)) ⋆ Eq (s160.At (x - 160))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (x - 168))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 T).toInt).At (x - 176))
      ⋆ Eq (s184.At (x - 184))
      ⋆ Eq (sp1.At (x - 224)) ⋆ Eq (sp2.At (x - 216)) ⋆ Eq (rslot.At (x - 232))
      ⋆ Eq (blk.At (x - 232 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s0.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq (tl.At base)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (recv + 8))
      ⋆ Eq ((ptrs ++ List.replicate (8 * (n - i)) 0).At A)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ O ⋆ R)
    (hno : NewobjectC Heap (label "type__" + @NOTY@).toBitVec 24 (144 + S)) (hlu : LuUAccC Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + @HEAD@) ∧ st.data.regs.rax.toNat = i + 1 ∧ st.data.regs.rdx.toNat = n
        ∧ st.data.regs.rcx.toNat = e ∧ st.data.regs.rbx = 0 ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsp = s0.regs.rsp ∧ st.data.regs.r14 = s0.regs.r14 ∧
        ∃ (p q : BitVec 64) (blk' rslot' sp1' sp2' s136' s152' s160' : List UInt8),
          blk'.length = 144 + S ∧ rslot'.length = 8 ∧ sp1'.length = 8 ∧ sp2'.length = 8 ∧ s136'.length = 8
          ∧ s152'.length = 8 ∧ s160'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
          ⋆ Eq ((Int.toBytes 8 recv.toInt).At (x + 8))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt).At (x + 32))
          ⋆ Eq ((Int.toBytes 8 base.toInt).At (x - 128)) ⋆ Eq (s136'.At (x - 136))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt).At (x - 144))
          ⋆ Eq (s152'.At (x - 152)) ⋆ Eq (s160'.At (x - 160))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (x - 168))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 T).toInt).At (x - 176))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 e).toInt).At (x - 184))
          ⋆ Eq (sp1'.At (x - 224)) ⋆ Eq (sp2'.At (x - 216)) ⋆ Eq (rslot'.At (x - 232))
          ⋆ Eq (blk'.At (x - 232 - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s0.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 24 - 8 * g.l.length)
          ⋆ Eq (tl.At base)
          ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (recv + 8))
          ⋆ Eq ((ptrs ++ Int.toBytes 8 p.toInt ++ List.replicate (8 * (n - (i + 1))) 0).At A)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ (Eq ((Int.toBytes 8 q.toInt).At p) ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (p + 8))
            ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (p + 16)) ⋆ Eq ((u64Bytes g.l).toList.At q) ⋆ O) ⋆ R)
          st.data.dmem)
      ⟨s0, Host.addrOf (k + @HEAD@)⟩ := by'''

LOOP = '''theorem lcl_loop [Host] (k : Nat) (hk : @CODE@.IsInfixAt Host.prog k)
    (hf : LabelsFresh @CODE@ k)
    (x base recv A : BitVec 64) (tl : List UInt8) (T : Nat) (gs : List ListU64) (hgs : ∀ g ∈ gs, g.ok)
    (hT : tl.length = T) (hn : gs.length ≤ 4) (hT32 : T < 2 ^ 32)
    (hend : lcStart gs gs.length = T)
    (hparts : ∀ i (hi : i < gs.length), (tl.drop (lcStart gs i)).take (4 + 8 * gs[i].l.length)
      = [4, 0, 0, 0] ++ (u64Bytes gs[i].l).toList)
    (hnexts : ∀ i, i + 1 < gs.length → (tl.drop (4 * (i + 1))).take 4 = (uintBytes 4 (lcStart gs (i + 1))).toList)
    (cap0 : Nat) (hcap : T + 4 ≤ cap0) (hcap63 : cap0 < 2 ^ 63)
    (S : Nat) (hS : S < 2 ^ 60) (ra rbp0 guard : UInt64) (Heap : Nat → DataMem → Prop) (R : DataMem → Prop)
    (hguard : guard.toNat + 400 + S < x.toNat) (hx : 400 + S ≤ x.toNat)
    (hno : NewobjectC Heap (label "type__" + @NOTY@).toBitVec 24 (144 + S)) (hlu : LuUAccC Heap S) :
    ∀ j i (s0 : MachineData) (acc : List (BitVec 64 × BitVec 64 × ListU64))
      (blk rslot sp1 sp2 s136 s152 s160 s184 : List UInt8) (avail : Nat),
    i + j = gs.length → acc.length = i → acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.2.2) = gs.take i →
    blk.length = 144 + S → rslot.length = 8 → sp1.length = 8 → sp2.length = 8 → s136.length = 8 →
    s152.length = 8 → s160.length = 8 → s184.length = 8 → 152 * j ≤ avail →
    s0.regs.rax.toNat = i → s0.regs.rdx.toNat = gs.length → s0.regs.rcx.toNat = lcStart gs i →
    s0.regs.rbx = 0 → s0.regs.rdi = 0 → s0.regs.rsp.toBitVec = x - 8#64 - 216 →
    (s0.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 recv.toInt).At (x + 8))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt).At (x + 32))
      ⋆ Eq ((Int.toBytes 8 base.toInt).At (x - 128)) ⋆ Eq (s136.At (x - 136))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt).At (x - 144))
      ⋆ Eq (s152.At (x - 152)) ⋆ Eq (s160.At (x - 160))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (x - 168))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 T).toInt).At (x - 176))
      ⋆ Eq (s184.At (x - 184))
      ⋆ Eq (sp1.At (x - 224)) ⋆ Eq (sp2.At (x - 216)) ⋆ Eq (rslot.At (x - 232))
      ⋆ Eq (blk.At (x - 232 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s0.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq (tl.At base)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (recv + 8))
      ⋆ Eq ((ptrBytes (acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1)) ++ List.replicate (8 * (gs.length - i)) 0).At A)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ lcObjs acc ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + @EXIT@) ∧ st.data.regs.rbx = 0 ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsp = s0.regs.rsp ∧ st.data.regs.r14 = s0.regs.r14 ∧
        ∃ (acc' : List (BitVec 64 × BitVec 64 × ListU64)) (avail' : Nat),
          acc'.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.2.2) = gs ∧
          (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
            ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (recv + 8))
            ⋆ Eq ((ptrBytes (acc'.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))).At A) ⋆ lcObjs acc' ⋆ Eq (tl.At base) ⋆ Heap avail'
            ⋆ R ⋆ lcStk x S ⋆ fun _ => True) st.data.dmem)
      ⟨s0, Host.addrOf (k + @HEAD@)⟩ := by
  intro j
  induction j with
  | zero =>
    intro i s0 acc blk rslot sp1 sp2 s136 s152 s160 s184 avail hij hacc hgsa hblk hrs hsp1 hsp2 h136 h152 h160 h184 _
      hrax hrdx _ hrbx hrdi _ h_mem
    have hi : i = gs.length := by omega
    subst hi
    have hacc' : acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.2.2) = gs := by rw [hgsa, List.take_length]
    refine lcl_exit k hk hf _ s0 (UInt64.toNat_inj.mp (by omega)) fun _ => ⟨rfl, hrbx, hrdi, rfl, rfl, acc, avail, hacc', ?_⟩
    rw [Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.append_nil] at h_mem
    obtain ⟨F, H1⟩ : ∃ F, ((Eq ((Int.toBytes 8 recv.toInt).At (x + 8))
        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt).At (x + 32))
        ⋆ Eq ((Int.toBytes 8 base.toInt).At (x - 128)) ⋆ Eq (s136.At (x - 136))
        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt).At (x - 144))
        ⋆ Eq (s152.At (x - 152)) ⋆ Eq (s160.At (x - 160))
        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (x - 168))
        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 T).toInt).At (x - 176))
        ⋆ Eq (s184.At (x - 184)) ⋆ Eq (sp2.At (x - 216)) ⋆ Eq (sp1.At (x - 224)) ⋆ Eq (rslot.At (x - 232))
        ⋆ Eq (blk.At (x - 232 - 144 - BitVec.ofNat 64 S)))
      ⋆ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (recv + 8))
      ⋆ Eq ((ptrBytes (acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))).At A) ⋆ lcObjs acc ⋆ Eq (tl.At base)
      ⋆ Heap avail ⋆ R ⋆ F)) s0.dmem := ⟨_, by ecancel⟩
    have H2 := lcs_mono (P' := lcStk x S) (fun m hm => ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
      Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, h136, Int.toBytes_length 8 _, h152, h160,
      Int.toBytes_length 8 _, Int.toBytes_length 8 _, h184, hsp2, hsp1, hrs, hblk, hm⟩) H1
    exact sep_true (P := Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (recv + 8))
      ⋆ Eq ((ptrBytes (acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))).At A) ⋆ lcObjs acc ⋆ Eq (tl.At base) ⋆ Heap avail ⋆ R
      ⋆ lcStk x S) (by ecancel)
  | succ j ih =>
    intro i s0 acc blk rslot sp1 sp2 s136 s152 s160 s184 avail hij hacc hgsa hblk hrs hsp1 hsp2 h136 h152 h160 h184 hav
      hrax hrdx hrcx hrbx hrdi hrsp h_mem
    have hi : i < gs.length := by omega
    have hg := hgs gs[i] (List.getElem_mem hi)
    have hse := lcStart_succ gs i hi
    have hle := lcStart_le gs (i + 1)
    refine eventually_trans _ _ _ _ (lcl_iter k hk hf x base recv A tl (ptrBytes (acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))) T
      gs.length i (lcStart gs i) (lcStart gs (i + 1)) gs[i] hg hT hn hi
      (by rw [ptrBytes_length]; simp [hacc]) hse.symm (by omega)
      (by simp only [lcStart]; omega) (hparts i hi) (hnexts i) (fun h => by rw [h, hend]) hT32 cap0 hcap hcap63
      S hS blk rslot sp1 sp2 s136 s152 s160 s184 hblk hrs hsp1 hsp2 h136 h152 h160 h184 ra rbp0 guard Heap avail (by omega)
      (lcObjs acc) R s0 hrax hrdx hrcx hrsp hguard hx h_mem hno hlu) ?_
    rintro ⟨d, pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, p, q, blk', rslot', sp1', sp2', s136', s152', s160',
      hb', hr', hs1', hs2', h136', h152', h160', Hm⟩
    dsimp only at hpc h1 h2 h3 h4 h5 h6 h7 Hm
    subst hpc
    have := ih (i + 1) d ((p, q, gs[i]) :: acc) blk' rslot' sp1' sp2' s136' s152' s160'
      (Int.toBytes 8 (BitVec.ofNat 64 (lcStart gs (i + 1))).toInt) (avail - 24 - 8 * gs[i].l.length)
      (by omega) (by simp [hacc])
      (by rw [List.reverse_cons, List.map_append, hgsa, List.take_add_one, List.getElem?_eq_getElem hi]; rfl)
      hb' hr' hs1' hs2' h136' h152' h160' (Int.toBytes_length 8 _) (by have : gs[i].l.length ≤ 16 := hg; omega) h1 h2 h3 h4 h5 (by rw [h6]; exact hrsp)
      (by
        rw [h7]
        simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, ptrBytes_snoc, lcObjs]
        exact Hm)
    refine eventually_trans _ _ _ _ this ?_
    rintro st ⟨g1, g2, g3, g4, g5, g6⟩
    exact Eventually.done _ ⟨g1, g2, g3, by rw [g4, h6], by rw [g5, h7], g6⟩'''

EXIT_STMT = '''theorem lcl_exit [Host] (k : Nat) (hk : @CODE@.IsInfixAt Host.prog k)
    (hf : LabelsFresh @CODE@ k) (P : MachineState → Prop) (s0 : MachineData)
    (hrr : s0.regs.rax = s0.regs.rdx)
    (hP : ∀ f : StatusFlags, P ⟨⟨s0.regs, s0.zmms, f, s0.dmem⟩, Host.addrOf (k + @EXIT@)⟩) :
    Eventually (step1 Host.exe) P ⟨s0, Host.addrOf (k + @HEAD@)⟩ := by'''

ACC_STMT = '''def accept_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : @CODE@.IsInfixAt Host.prog k)
    (hf : LabelsFresh @CODE@ k)
    (tl : List UInt8) (T : Nat) (gs : List ListU64) (hgs : ∀ g ∈ gs, g.ok)
    (hT : tl.length = T) (hn1 : 1 ≤ gs.length) (hn : gs.length ≤ 4) (hT32 : T < 2 ^ 32)
    (hend : lcStart gs gs.length = T)
    (hfirst : tl.take 4 = (uintBytes 4 (4 * gs.length)).toList)
    (hparts : ∀ i (hi : i < gs.length), (tl.drop (lcStart gs i)).take (4 + 8 * gs[i].l.length)
      = [4, 0, 0, 0] ++ (u64Bytes gs[i].l).toList)
    (hnexts : ∀ i, i + 1 < gs.length → (tl.drop (4 * (i + 1))).take 4 = (uintBytes 4 (lcStart gs (i + 1))).toList)
    (s : MachineData) (ra guard : UInt64) (fp slot s8 s32 l128 l136 l144 l152 l160 l168 l176 l184 l208 l216 l224 rslot blk
      cP cL cC : List UInt8)
    (hfp : fp.length = 8) (hsl : slot.length = 8) (h8 : s8.length = 8) (h32 : s32.length = 8)
    (hl128 : l128.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl152 : l152.length = 8)
    (hl160 : l160.length = 8) (hl168 : l168.length = 8) (hl176 : l176.length = 8) (hl184 : l184.length = 8)
    (hl208 : l208.length = 8) (hl216 : l216.length = 8) (hl224 : l224.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (S : Nat) (hS : S < 2 ^ 60) (hblk : blk.length = 144 + S)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 8 * 4 + 152 * 4 ≤ avail)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
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
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq ((tl.take 4).At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq ((tl.drop 4).At (s.regs.rbx.toBitVec + 4 + 4))
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 400 + S < s.regs.rsp.toNat) (hsp : 400 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + T) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hms : MakesliceC Heap (label "type__" + @MSTY@).toBitVec 8 (144 + S))
    (hno : NewobjectC Heap (label "type__" + @NOTY@).toBitVec 24 (144 + S)) (hlu : LuUAccC Heap S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧
        ∃ (A : BitVec 64) (acc : List (BitVec 64 × BitVec 64 × ListU64)) (avail' : Nat),
          acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.2.2) = gs ∧
          (Eq ((Int.toBytes 8 A.toInt).At s.regs.rax.toBitVec)
            ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (s.regs.rax.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (s.regs.rax.toBitVec + 16))
            ⋆ Eq ((ptrBytes (acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))).At A)
            ⋆ lcObjs acc ⋆ Eq (tl.At (s.regs.rbx.toBitVec + 4)) ⋆ Heap avail'
            ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
            ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16)) ⋆ lcStk s.regs.rsp.toBitVec S
            ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩'''

ACC_PRE = '''  have hT4 : 4 ≤ T := by have := congrArg List.length hfirst; simp [Fv.uintBytes_size] at this; omega
  have ho4 : (tl.take 4).length = 4 := by simp; omega
  have hoff : Int.ofBytes (tl.take 4) = ((4 * gs.length : Nat) : Int) := by
    rw [hfirst, ofBytes_uintBytes4 _ (by omega)]
  have hle4n : 4 * gs.length ≤ T := by
    have := lcStart_le gs 0; rw [hend] at this; simp [lcStart] at this; omega
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *'''

ACC_LOOP = '''  have hrcx4 : 4 ≤ rcx.toNat := by omega
  have hrdi4 : 4 ≤ rdi.toNat := by omega
  rw [lca_m4 _ (by simpa using hrdi4), lca_m4' _ (by simpa using hrcx4), BitVec.mul_one,
    show rcx.toBitVec.toNat - 4 = T by simp; omega] at N11
  rw [show Int.toBytes 8 rdi.toBitVec.toInt = Int.toBytes 8 (BitVec.ofNat 64 rdi.toBitVec.toNat).toInt by simp] at N11
  have hstart : lcStart gs 0 = 4 * gs.length := by simp [lcStart]
  have htl : Eq (tl.At (rbx.toBitVec + 4)) = Eq ((tl.take 4).At (rbx.toBitVec + 4))
      ⋆ Eq ((tl.drop 4).At (rbx.toBitVec + 4 + 4)) := by
    conv => lhs; rw [← List.take_append_drop 4 tl]
    exact at_app _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; rfl) (by simp; omega)
  refine eventually_trans _ _ _ _ (lcl_loop k hk hf rsp.toBitVec (rbx.toBitVec + 4) rax.toBitVec rax1.toBitVec tl T gs hgs
    hT hn hT32 hend hparts hnexts rdi.toBitVec.toNat (by simp; omega) (by simpa using hcap63) S hS ra rbp guard Heap
    (Eq ((Int.toBytes 8 rbx.toBitVec.toInt).At (rsp.toBitVec + 16)) ⋆ Eq ([4, 0, 0, 0].At rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (rax.toBitVec + 16))
      ⋆ Eq (((sm1.drop 8).drop 8).At (rsp.toBitVec - 208)) ⋆ R)
    hguard hsp hno hlu gs.length 0 _ [] stk1
    (Int.toBytes 8 (Host.addrOf (k + @MSCALL@ + 1)).toBitVec.toInt) (sm1.take 8) ((sm1.drop 8).take 8) l136
    (Int.toBytes 8 (BitVec.ofNat 64 (4 * gs.length)).toInt) l160 l184 (avail - 8 * gs.length)
    (by omega) rfl rfl hstk1 (Int.toBytes_length 8 _) (by simp [hsm1]) (by simp [hsm1]) hl136 (Int.toBytes_length 8 _) hl160 hl184
    (by omega) (by simp) (by show (BitVec.ofNat 64 gs.length).toNat = _; simp; omega)
    (by show (BitVec.ofNat 64 (4 * gs.length)).toNat = _; rw [hstart]; simp; omega)
    (by apply UInt64.toBitVec_inj.mp; simp) (by apply UInt64.toBitVec_inj.mp; simp)
    (by simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)
    (by
      dsimp only
      simp only [List.reverse_nil, List.map_nil, show ptrBytes [] = [] from rfl, List.nil_append, Nat.sub_zero,
        lcObjs, Std.ExtHashMap.sep_emp]
      rw [htl]
      ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrbx2, hrdi2, hrsp2, hr142, acc', av', hacc', Hm2⟩
  dsimp only at hpc2 hrbx2 hrdi2 hrsp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrbx2 hrdi2 hrsp2 hr142 Hm2
  subst hrbx2 hrdi2 hrsp2'''

ACC_FIN = '''  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, rfl, rfl, ?_, rax1.toBitVec, acc', av', hacc', ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · exact sep_true (P := Eq ((Int.toBytes 8 rax1.toBitVec.toInt).At rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (rax.toBitVec + 16))
      ⋆ Eq ((ptrBytes (acc'.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))).At rax1.toBitVec)
      ⋆ lcObjs acc' ⋆ Eq (tl.At (rbx.toBitVec + 4)) ⋆ Heap av'
      ⋆ Eq ([4, 0, 0, 0].At rbx.toBitVec) ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbx.toBitVec.toInt).At (rsp.toBitVec + 16)) ⋆ lcStk rsp.toBitVec S ⋆ R) (by ecancel)'''

EMP_STMT = '''def accept_empty_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : @CODE@.IsInfixAt Host.prog k)
    (hf : LabelsFresh @CODE@ k)
    (s : MachineData) (ra guard : UInt64) (fp slot cP cLC : List UInt8) (hfp : fp.length = 8)
    (hsl : slot.length = 8) (hcP : cP.length = 8) (hcLC : cLC.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cLC.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 232 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hx15 : s.zmms.get (AvxReg.xmm RegMm.mm15) = 0),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq ((Int.toBytes 8 (label "runtime.zerobase").toBitVec.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((List.replicate 16 0).At (s.regs.rax.toBitVec + 8))
          ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩'''

EMP_FIN = '''  apply Eventually.done
  simp only
  refine ⟨trivial, UInt64.toBitVec_inj.mp (by simp), UInt64.toBitVec_inj.mp (by simp),
    UInt64.toBitVec_inj.mp (by simp), trivial, ?_⟩
  refine sep_mono_right' (Q := ?Q) (fun _ _ => trivial) ?h
  case h => ecancel'''
ACC_MS = '''  apply store_step_at _ _ (rsp.toBitVec - 232) _ _ _ rslot _ _ (lcl_ret _) (by ecancel) (by exact hrs)
  intro n8 N8
  simp only [Width.bytes, Width.bits] at N8
  kunfold
  rw [lcl_ret] at *
  have hn4 : 4 * gs.length / 4 = gs.length := by omega
  rw [hn4]
  have hsp3 : ∀ (a b c : List UInt8), a.length = 8 → b.length = 8 → c.length = 8 →
      Eq ((a ++ (b ++ c)).At (rsp.toBitVec - 232 + 8)) = Eq (a.At (rsp.toBitVec - 224)) ⋆ Eq (b.At (rsp.toBitVec - 216))
        ⋆ Eq (c.At (rsp.toBitVec - 208)) := by
    intro a b c ha hb hc
    rw [at_app a _ (b := rsp.toBitVec - 216) (by rw [ha]; bv_omega) (by simp [*]),
      at_app b c (b := rsp.toBitVec - 208) (by rw [hb]; bv_omega) (by simp [*]), show rsp.toBitVec - 232 + 8 = rsp.toBitVec - 224 by bv_omega]
    simp only [Std.ExtHashMap.sep_assoc]
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + @MSCALL@ + 1)) gs.length avail blk (l224 ++ (l216 ++ l208)) _ rfl
    (by show (BitVec.ofNat 64 gs.length).toNat ≤ _; simp; omega)
    (by show (BitVec.ofNat 64 gs.length).toNat = _; simp; omega) (by omega) (by unfold maxAlloc; omega) (by omega) hblk
    (by simp [*]) (by dsimp only; rw [lcl_blk, hsp3 _ _ _ hl224 hl216 hl208]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, -, stk1, sm1, hstk1, hsm1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hr141 Hm1
  subst hrsp1 hr141
  rw [lcl_blk, hn4, ← List.take_append_drop 8 sm1, ← List.take_append_drop 8 (sm1.drop 8),
    hsp3 _ _ _ (by simp [hsm1]) (by simp [hsm1]) (by simp [hsm1])] at Hm1'''

# ---- r8 offset-order reject: copied from Fk/LcOrder.lean (lcl_order statement, its reject block from the
# label of the convT64/fmt.errorf block on (@B<k>@ = directive block + k, @NOCALL@ = newobject call site),
# lc_reject_offset_order_main statement, proof head and tail after the loop-head label). Format string
# and type word names (@FMT@, @FMTA@, @FMTLEN@, @U64T@) come from the include adapter.

ORD_STMT = '''theorem lcl_order [Host] (k : Nat) (hk : @CODE@.IsInfixAt Host.prog k)
    (hf : LabelsFresh @CODE@ k)
    (x base recv A : BitVec 64) (tl ptrs : List UInt8) (T n i s e : Nat)
    (hT : tl.length = T) (hn : n ≤ 4) (hi : i + 1 < n) (hptrs : ptrs.length = 8 * i)
    (hes : e < s) (hs4 : 4 * n ≤ s) (hsT : s ≤ T)
    (hnext : i + 1 < n → (tl.drop (4 * (i + 1))).take 4 = (uintBytes 4 e).toList)
    (hT32 : T < 2 ^ 32) (cap0 : Nat) (hcap : T + 4 ≤ cap0) (hcap63 : cap0 < 2 ^ 63)
    (S : Nat) (hS : S < 2 ^ 60) (blk rslot sp1 sp2 sp3 s200 s192 s136 s152 s160 s184 a0 a1 : List UInt8)
    (hblk : blk.length = 144 + S) (hrs : rslot.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (hsp3 : sp3.length = 8) (h200 : s200.length = 8) (h192 : s192.length = 8)
    (h136 : s136.length = 8) (h152 : s152.length = 8) (h160 : s160.length = 8) (h184 : s184.length = 8)
    (ha0 : a0.length = 16) (ha1 : a1.length = 16)
    (ra rbp0 guard : UInt64) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 24 + 16 + 67 + 40 + 8192 ≤ avail)
    (O R : DataMem → Prop) (s0 : MachineData)
    (hrax : s0.regs.rax.toNat = i) (hrdx : s0.regs.rdx.toNat = n) (hrcx : s0.regs.rcx.toNat = s)
    (hrsp : s0.regs.rsp.toBitVec = x - 8#64 - 216)
    (hguard : guard.toNat + 400 + S < x.toNat) (hx : 400 + S ≤ x.toNat)
    (h_mem : s0.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 recv.toInt).At (x + 8))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt).At (x + 32))
      ⋆ Eq ((Int.toBytes 8 base.toInt).At (x - 128)) ⋆ Eq (s136.At (x - 136))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt).At (x - 144))
      ⋆ Eq (s152.At (x - 152)) ⋆ Eq (s160.At (x - 160))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (x - 168))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 T).toInt).At (x - 176))
      ⋆ Eq (s184.At (x - 184))
      ⋆ Eq (sp1.At (x - 224)) ⋆ Eq (sp2.At (x - 216)) ⋆ Eq (rslot.At (x - 232))
      ⋆ Eq (blk.At (x - 232 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s0.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq (tl.At base)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (recv + 8))
      ⋆ Eq ((ptrs ++ List.replicate (8 * (n - i)) 0).At A)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (sp3.At (x - 208)) ⋆ Eq (s200.At (x - 200)) ⋆ Eq (s192.At (x - 192))
      ⋆ Eq (a0.At (x - 104)) ⋆ Eq (a1.At (x - 88)) ⋆ Eq (@FMT@.At @FMTA@)
      ⋆ StaticBox (BitVec.ofNat 64 e) ⋆ StaticBox (BitVec.ofNat 64 s) ⋆ O ⋆ R)
    (hno : NewobjectC Heap (label "type__" + @NOTY@).toBitVec 24 (144 + S))
    (hcv : ConvT64C Heap (144 + S)) (hfe : FmtErrorfDDC Heap @FMT@ @U64T@ (144 + S)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp.toBitVec = x + 8 ∧ st.data.regs.rbp = rbp0 ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s0, Host.addrOf (k + @HEAD@)⟩ := by'''

ORD_ERR = '''  kat hk @CODE@ @B0@
  kat hk @CODE@ @B1@
  kat hk @CODE@ @B2@
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [lcl_g, show x - 224 + 120 = x - 104 by bv_omega]
  apply store_avx_step _ _ _ _ a0 _ _ (by ecancel) (by exact ha0) (by decide)
  intro m6 H6
  kunfold
  kat hk @CODE@ @B3@
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show x - 104 + 16 = x - 88 by bv_omega]
  apply store_avx_step _ _ _ _ a1 _ _ (by ecancel) (by exact ha1) (by decide)
  intro m7 H7
  kunfold
  kat hk @CODE@ @B4@
  kat hk @CODE@ @B5@
  kat hk @CODE@ @B6@
  apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + @NOCALL@ + 1)).toBitVec.toInt) _ _
    (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  rw [lcl_call] at *
  refine eventually_trans _ _ _ _ (hcv _ (Host.addrOf (k + @B6@ + 1)) (avail - 24) stk1 sn1 _ (by omega) hstk1 hsn1
    (by dsimp only; rw [lcl_blk, hspA]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, stk2, sn2, hb1, av1, hstk2, hsn2, hbox1, hav1, hav1', Hm2⟩
  dsimp only at hpc2 hrsp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 Hm2
  subst hrsp2
  rw [lcl_blk, hspA] at Hm2
  rw [lr_split16 _ (Int.toBytes_length 16 _) (x - 104), lr_split16 _ (Int.toBytes_length 16 _) (x - 88)] at Hm2
  kat hk @CODE@ @B7@
  kat hk @CODE@ @B8@
  rw [lcl_g, show x - 224 + 120 = x - 104 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk @CODE@ @B9@
  rw [lcl_g, show x - 224 + 128 = x - 104 + 8 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk @CODE@ @B10@
  rw [lcl_g, show x - 224 + 40 = x - 184 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk @CODE@ @B11@
  kat hk @CODE@ @B12@
  apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + @B6@ + 1)).toBitVec.toInt) _ _
    (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  rw [lcl_call] at *
  have hrcxs : rcx.toBitVec = BitVec.ofNat 64 s := by apply BitVec.eq_of_toNat_eq; simp; omega
  refine eventually_trans _ _ _ _ (hcv _ (Host.addrOf (k + @B12@ + 1)) av1 stk2 sn2 _ (by omega) hstk2 hsn2
    (by dsimp only; rw [lcl_blk, hspA, staticBox_congr hrcxs]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, stk3, sn3, hb2, av2, hstk3, hsn3, hbox2, hav2, hav2', Hm3⟩
  dsimp only at hpc3 hrsp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 Hm3
  subst hrsp3
  rw [lcl_blk, hspA, staticBox_congr hrcxs] at Hm3
  kat hk @CODE@ @B13@
  kat hk @CODE@ @B14@
  rw [lcl_g, show x - 224 + 136 = x - 88 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk @CODE@ @B15@
  rw [lcl_g, show x - 224 + 144 = x - 88 + 8 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  kat hk @CODE@ @B16@
  kat hk @CODE@ @B17@
  kat hk @CODE@ @B18@
  kat hk @CODE@ @B19@
  kat hk @CODE@ @B20@
  kat hk @CODE@ @B21@
  apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + @B12@ + 1)).toBitVec.toInt) _ _
    (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  rw [lcl_call] at *
  simp only [@FMTA@] at H14
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + @B21@ + 1)) av2 hb1 hb2 stk3 (sn3 ++ (sp2 ++ (sp3 ++ (s200 ++ s192))))
    rax2.toBitVec (BitVec.ofNat 64 e) rax3.toBitVec (BitVec.ofNat 64 s) _
    (by rw [@FMTLEN@]; rfl) (by first | rfl | decide) (by first | rfl | decide)
    hbox1 (hrcxs ▸ hbox2) hstk3 (by simp [hsn3, hsp2, hsp3, h200, h192]) (by rw [@FMTLEN@]; omega)
    (by dsimp only
        simp only [@U64T@, List.append_assoc]
        rw [lcl_g, show x - 224 + 120 = x - 104 by bv_omega,
          at_app sn3 _ (b := x - 216) (by rw [hsn3]; bv_omega) (by simp [hsn3, hsp2, hsp3, h200, h192]),
          join4 (x - 216) (x - 208) (x - 200) (x - 192) _ _ _ _ hsp2 hsp3 h200 h192 (by bv_omega) (by bv_omega) (by bv_omega),
          join4 (x - 104) (x - 104 + 8) (x - 88) (x - 88 + 8) _ _ _ _ (Int.toBytes_length 8 _)
            (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (by bv_omega) (by bv_omega) (by bv_omega),
          lcl_blk, hspA]
        ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrax4, stk4, sp4, av4, hstk4, hsp4, hav4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrax4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hrax4 Hm4
  subst hrsp4
  kat hk @CODE@ @B22@
  intro _
  kat hk @CODE@ @B23@
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hrax4 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf @CODE@ @B32@
  kat hk @CODE@ @B32@
  kat hk @CODE@ @B33@
  kat hk @CODE@ @B34@
  rw [show (216 : BitVec 64) + ({ toBitVec := x - 232 } + 8 : UInt64).toBitVec = x - 8 by
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk @CODE@ @B35@
  rw [show x - 8 + 8#64 = x by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, hrax4, ?_, ?_, ?_⟩
  · first | (simp; done) | (simp; bv_omega)
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · exact sep_true (by ecancel)'''

ORD_MAIN_STMT = '''def reject_order_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : @CODE@.IsInfixAt Host.prog k)
    (hf : LabelsFresh @CODE@ k)
    (tl : List UInt8) (T n e : Nat) (hT : tl.length = T) (hn2 : 2 ≤ n) (hn : n ≤ 4) (hT32 : T < 2 ^ 32)
    (hle4n : 4 * n ≤ T) (he : e < 4 * n)
    (hfirst : tl.take 4 = (uintBytes 4 (4 * n)).toList)
    (hsecond : (tl.drop 4).take 4 = (uintBytes 4 e).toList)
    (s : MachineData) (ra guard : UInt64) (fp slot s8 s32 l128 l136 l144 l152 l160 l168 l176 l184 l192 l200 l208 l216 l224
      rslot blk cP cL cC a0 a1 : List UInt8)
    (hfp : fp.length = 8) (hsl : slot.length = 8) (h8 : s8.length = 8) (h32 : s32.length = 8)
    (hl128 : l128.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl152 : l152.length = 8)
    (hl160 : l160.length = 8) (hl168 : l168.length = 8) (hl176 : l176.length = 8) (hl184 : l184.length = 8)
    (hl192 : l192.length = 8) (hl200 : l200.length = 8)
    (hl208 : l208.length = 8) (hl216 : l216.length = 8) (hl224 : l224.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8) (ha0 : a0.length = 16) (ha1 : a1.length = 16)
    (S : Nat) (hS : S < 2 ^ 60) (hblk : blk.length = 144 + S)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 + 24 + 16 + 67 + 40 + 8192 ≤ avail)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
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
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq ((tl.take 4).At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq ((tl.drop 4).At (s.regs.rbx.toBitVec + 4 + 4))
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (l200.At (s.regs.rsp.toBitVec - 200)) ⋆ Eq (l192.At (s.regs.rsp.toBitVec - 192))
      ⋆ Eq (a0.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (a1.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (@FMT@.At @FMTA@)
      ⋆ StaticBox (BitVec.ofNat 64 e) ⋆ StaticBox (BitVec.ofNat 64 (4 * n)) ⋆ R)
    (hguard : guard.toNat + 400 + S < s.regs.rsp.toNat) (hsp : 400 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + T) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hms : MakesliceC Heap (label "type__" + @MSTY@).toBitVec 8 (144 + S))
    (hno : NewobjectC Heap (label "type__" + @NOTY@).toBitVec 24 (144 + S))
    (hcv : ConvT64C Heap (144 + S)) (hfe : FmtErrorfDDC Heap @FMT@ @U64T@ (144 + S)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩'''

ORD_MAIN_PRE = '''  have hT4 : 4 ≤ T := by omega
  have ho4 : (tl.take 4).length = 4 := by simp; omega
  have hoff : Int.ofBytes (tl.take 4) = ((4 * n : Nat) : Int) := by
    rw [hfirst, ofBytes_uintBytes4 _ (by omega)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *'''

ORD_MAIN_TAIL = '''  have hrcx4 : 4 ≤ rcx.toNat := by omega
  have hrdi4 : 4 ≤ rdi.toNat := by omega
  rw [lca_m4 _ (by simpa using hrdi4), lca_m4' _ (by simpa using hrcx4), BitVec.mul_one,
    show rcx.toBitVec.toNat - 4 = T by simp; omega] at N11
  rw [show Int.toBytes 8 rdi.toBitVec.toInt = Int.toBytes 8 (BitVec.ofNat 64 rdi.toBitVec.toNat).toInt by simp] at N11
  have htl : Eq (tl.At (rbx.toBitVec + 4)) = Eq ((tl.take 4).At (rbx.toBitVec + 4))
      ⋆ Eq ((tl.drop 4).At (rbx.toBitVec + 4 + 4)) := by
    conv => lhs; rw [← List.take_append_drop 4 tl]
    exact at_app _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; rfl) (by simp; omega)
  refine eventually_trans _ _ _ _ (lcl_order k hk hf rsp.toBitVec (rbx.toBitVec + 4) rax.toBitVec rax1.toBitVec tl []
    T n 0 (4 * n) e hT hn (by omega) rfl he (Nat.le_refl _) hle4n (fun _ => by simpa using hsecond) hT32
    rdi.toBitVec.toNat (by simp; omega) (by simpa using hcap63) S hS stk1
    (Int.toBytes 8 (Host.addrOf (k + @MSCALL@ + 1)).toBitVec.toInt) (sm1.take 8) ((sm1.drop 8).take 8) ((sm1.drop 8).drop 8)
    l200 l192 l136 (Int.toBytes 8 (BitVec.ofNat 64 (4 * n)).toInt) l160 l184 a0 a1
    hstk1 (Int.toBytes_length 8 _) (by simp [hsm1]) (by simp [hsm1]) (by simp [hsm1]) hl200 hl192 hl136
    (Int.toBytes_length 8 _) hl160 hl184 ha0 ha1 ra rbp guard Heap (avail - 8 * n) (by omega)
    (Eq ((Int.toBytes 8 rbx.toBitVec.toInt).At (rsp.toBitVec + 16)) ⋆ Eq ([4, 0, 0, 0].At rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (rax.toBitVec + 16))) R _
    (by simp) (by show (BitVec.ofNat 64 n).toNat = _; simp; omega)
    (by show (BitVec.ofNat 64 (4 * n)).toNat = _; simp; omega)
    (by simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega) hguard hsp
    (by
      dsimp only
      simp only [List.nil_append, Nat.sub_zero]
      rw [htl]
      ecancel) hno hcv hfe) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrsp2, hrbp2, Hm2⟩
  dsimp only at hpc2 hrax2 hrsp2 hrbp2 Hm2
  refine Eventually.done _ ⟨hpc2, hrax2, ?_, hrbp2, Hm2⟩
  apply UInt64.toBitVec_inj.mp; rw [hrsp2]; simp'''

# ---- r9 element-decode error: copied from Fk/LcItems.lean (lcl_itemerr statement, its decoder call under
# LuURejShortC, its reject block from the label of the fmt.errorf("Items: %w") block on, lc_reject_item_main
# statement, proof head and tail after the loop-head label). @LUCALL@ = element decoder call site.

ITM_STMT = '''theorem lcl_itemerr [Host] (k : Nat) (hk : @CODE@.IsInfixAt Host.prog k)
    (hf : LabelsFresh @CODE@ k)
    (x base recv A : BitVec 64) (tl ptrs : List UInt8) (T n i s e : Nat)
    (hT : tl.length = T) (hn : n ≤ 4) (hi : i < n) (hl' : i + 1 = n) (hptrs : ptrs.length = 8 * i)
    (hse : s < e) (heT : e ≤ T) (hshort : e - s < 4) (hs4 : 4 * n ≤ s)
    (hlast : i + 1 = n → e = T)
    (hT32 : T < 2 ^ 32) (cap0 : Nat) (hcap : T + 4 ≤ cap0) (hcap63 : cap0 < 2 ^ 63)
    (S : Nat) (hS : S < 2 ^ 60) (blk rslot sp1 sp2 sp3 s200 s192 s136 s152 s160 s184 b0 : List UInt8)
    (hblk : blk.length = 144 + S) (hrs : rslot.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (hsp3 : sp3.length = 8) (h200 : s200.length = 8) (h192 : s192.length = 8)
    (h136 : s136.length = 8) (h152 : s152.length = 8) (h160 : s160.length = 8) (h184 : s184.length = 8)
    (hb0 : b0.length = 16)
    (ra rbp0 guard e0 e1 : UInt64) (ity msg hm : List UInt8) (sp : BitVec 64) (hity : ity.length = 8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec)
    (hit : (label "go_itab._errors.errorString_error").toBitVec ≠ 0)
    (RO : DataMem → Prop) (MsgIn : BitVec 64 → List UInt8 → List UInt8 → Prop) (hmsg : MsgIn sp msg hm)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 24 + 9 + msg.length + 8192 ≤ avail)
    (O R : DataMem → Prop) (s0 : MachineData)
    (hrax : s0.regs.rax.toNat = i) (hrdx : s0.regs.rdx.toNat = n) (hrcx : s0.regs.rcx.toNat = s)
    (hrsp : s0.regs.rsp.toBitVec = x - 8#64 - 216)
    (hguard : guard.toNat + 400 + S < x.toNat) (hx : 400 + S ≤ x.toNat)
    (h_mem : s0.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 recv.toInt).At (x + 8))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt).At (x + 32))
      ⋆ Eq ((Int.toBytes 8 base.toInt).At (x - 128)) ⋆ Eq (s136.At (x - 136))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt).At (x - 144))
      ⋆ Eq (s152.At (x - 152)) ⋆ Eq (s160.At (x - 160))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (x - 168))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 T).toInt).At (x - 176))
      ⋆ Eq (s184.At (x - 184))
      ⋆ Eq (sp1.At (x - 224)) ⋆ Eq (sp2.At (x - 216)) ⋆ Eq (rslot.At (x - 232))
      ⋆ Eq (blk.At (x - 232 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s0.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq (tl.At base)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (recv + 8))
      ⋆ Eq ((ptrs ++ List.replicate (8 * (n - i)) 0).At A)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (sp3.At (x - 208)) ⋆ Eq (s200.At (x - 200)) ⋆ Eq (s192.At (x - 192))
      ⋆ Eq (b0.At (x - 120)) ⋆ Eq (@FMT@.At @FMTA@)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrObj e1.toBitVec sp msg ⋆ Eq (hm.At sp) ⋆ RO ⋆ O ⋆ R)
    (hno : NewobjectC Heap (label "type__" + @NOTY@).toBitVec 24 (144 + S))
    (hlu : LuURejShortC S) (hfe : FmtErrorfWC Heap @FMT@ RO MsgIn (144 + S)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp.toBitVec = x + 8 ∧ st.data.regs.rbp = rbp0 ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s0, Host.addrOf (k + @HEAD@)⟩ := by'''

ITM_CALL = '''  have hrcx' : rcx.toBitVec = BitVec.ofNat 64 s := by apply BitVec.eq_of_toNat_eq; simp; omega
  have hy : (BitVec.ofNat 64 cap0 - rcx.toBitVec + -4).toNat = cap0 - s - 4 := by
    rw [hrcx']; exact lcl_y cap0 s (by omega) hcap63
  rw [lc_mask _ _ (by rw [hy]; omega) (by rw [hy]; omega)]
  rw [show rcx.toBitVec + base * 1#64 = base + BitVec.ofNat 64 s by rw [hrcx', BitVec.mul_one, BitVec.add_comm]]
  apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + @NOCALL@ + 1)).toBitVec.toInt) _ _
    (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  rw [lcl_call] at *
  have hx232 : (x - 232).toNat = x.toNat - 232 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  refine eventually_trans _ _ _ _ (hlu _ (Host.addrOf (k + @LUCALL@ + 1)) stk1 sp2 guard e0 e1 _ hstk1 hsp2
    (by show (BitVec.ofNat 64 e - rcx.toBitVec).toNat < 4; rw [hrcx']; simp [BitVec.toNat_sub]; omega)
    (by show guard.toNat < (x - 232).toNat - 8; rw [hx232]; omega)
    (by show 8 ≤ (x - 232).toNat; rw [hx232]; omega)
    (by dsimp only; rw [show x - 232 + 16 = x - 216 by bv_omega]; ecancel)) ?_
  have he0' : e0 ≠ 0 := fun h => hit (by rw [← he0, h]; rfl)
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hr142, stk2, sp2', hstk2, hsp2', Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrsp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrax2 hrbx2 hrsp2 hr142 Hm2
  subst hrax2 hrbx2 hrsp2
  rw [show x - 232 + 16 = x - 216 by bv_omega] at Hm2'''

ITM_ERR = '''  kat hk @CODE@ @B0@
  kat hk @CODE@ @B1@
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [lcl_g, show x - 224 + 104 = x - 120 by bv_omega]
  apply store_avx_step _ _ _ _ b0 _ _ (by ecancel) (by exact hb0) (by decide)
  intro m8 H8
  kunfold
  kat hk @CODE@ @B2@
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact he0' (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  kat hk @CODE@ @B3@
  apply load_step_at _ _ ((label "go_itab._errors.errorString_error").toBitVec + 8) _ _ ity _ _ (by rw [he0])
    (by ecancel) (by exact hity)
  kunfold
  kat hk @CODE@ @B4@
  kat hk @CODE@ @B5@
  rw [lr_split16 _ (Int.toBytes_length 16 _) (x - 120)] at H8
  rw [lcl_g, show x - 224 + 104 = x - 120 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms2.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m9 H9
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl ity hity] at H9
  kunfold
  kat hk @CODE@ @B6@
  rw [lcl_g, show x - 224 + 112 = x - 120 + 8 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms2.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk @CODE@ @B7@
  kat hk @CODE@ @B8@
  kat hk @CODE@ @B9@
  kat hk @CODE@ @B10@
  kat hk @CODE@ @B11@
  kat hk @CODE@ @B12@
  apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + @LUCALL@ + 1)).toBitVec.toInt) _ _
    (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  rw [lcl_call] at *
  try simp only [@FMTA@] at H11
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + @B12@ + 1)) (avail - 24) ity msg hm stk2
    (sn1 ++ (sp2' ++ (sp3 ++ (s200 ++ s192)))) rbx2.toBitVec sp _
    (by rw [@FMTLEN@]; rfl) (by first | rfl | decide) (by first | rfl | decide) hity hmsg hstk2
    (by simp [hsn1, hsp2', hsp3, h200, h192]) (by rw [@FMTLEN@]; omega)
    (by dsimp only
        rw [lcl_g, show x - 224 + 104 = x - 120 by bv_omega,
          at_app sn1 _ (b := x - 216) (by rw [hsn1]; bv_omega) (by simp [hsn1, hsp2', hsp3, h200, h192]),
          join4 (x - 216) (x - 208) (x - 200) (x - 192) _ _ _ _ hsp2' hsp3 h200 h192 (by bv_omega) (by bv_omega) (by bv_omega),
          at_app ity _ (b := x - 120 + 8) (by rw [hity]; bv_omega) (by simp [hity, Int.toBytes_length]),
          hspA, lcl_blk]
        ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrax4, stk4, sp4, av4, hstk4, hsp4, hav4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrax4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hrax4 Hm4
  subst hrsp4
  kat hk @CODE@ @B13@
  intro _
  kat hk @CODE@ @B14@
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hrax4 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf @CODE@ @B24@
  kat hk @CODE@ @B24@
  kat hk @CODE@ @B25@
  kat hk @CODE@ @B26@
  rw [show (216 : BitVec 64) + ({ toBitVec := x - 232 } + 8 : UInt64).toBitVec = x - 8 by
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk @CODE@ @B27@
  rw [show x - 8 + 8#64 = x by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, hrax4, ?_, ?_, ?_⟩
  · first | (simp; done) | (simp; bv_omega)
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · exact sep_true (by ecancel)'''

ITM_MAIN_STMT = '''def reject_item_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : @CODE@.IsInfixAt Host.prog k)
    (hf : LabelsFresh @CODE@ k)
    (tl : List UInt8) (T n : Nat) (hT : tl.length = T) (hn1 : n = 1) (hn : n ≤ 4) (hT32 : T < 2 ^ 32)
    (hle4n : 4 * n < T) (hshort : T < 8)
    (hfirst : tl.take 4 = (uintBytes 4 (4 * n)).toList)
    (s : MachineData) (ra guard : UInt64) (fp slot s8 s32 l128 l136 l144 l152 l160 l168 l176 l184 l192 l200 l208 l216 l224
      rslot blk cP cL cC b0 : List UInt8)
    (hfp : fp.length = 8) (hsl : slot.length = 8) (h8 : s8.length = 8) (h32 : s32.length = 8)
    (hl128 : l128.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl152 : l152.length = 8)
    (hl160 : l160.length = 8) (hl168 : l168.length = 8) (hl176 : l176.length = 8) (hl184 : l184.length = 8)
    (hl192 : l192.length = 8) (hl200 : l200.length = 8)
    (hl208 : l208.length = 8) (hl216 : l216.length = 8) (hl224 : l224.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8) (hb0 : b0.length = 16)
    (S : Nat) (hS : S < 2 ^ 60) (hblk : blk.length = 144 + S)
    (e0 e1 : UInt64) (ity msg hm : List UInt8) (sp : BitVec 64) (hity : ity.length = 8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec)
    (hit : (label "go_itab._errors.errorString_error").toBitVec ≠ 0)
    (RO : DataMem → Prop) (MsgIn : BitVec 64 → List UInt8 → List UInt8 → Prop) (hmsg : MsgIn sp msg hm)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 + 24 + 9 + msg.length + 8192 ≤ avail)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
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
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq ((tl.take 4).At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq ((tl.drop 4).At (s.regs.rbx.toBitVec + 4 + 4))
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (l200.At (s.regs.rsp.toBitVec - 200)) ⋆ Eq (l192.At (s.regs.rsp.toBitVec - 192))
      ⋆ Eq (b0.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (@FMT@.At @FMTA@)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrObj e1.toBitVec sp msg ⋆ Eq (hm.At sp) ⋆ RO ⋆ R)
    (hguard : guard.toNat + 400 + S < s.regs.rsp.toNat) (hsp : 400 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + T) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hms : MakesliceC Heap (label "type__" + @MSTY@).toBitVec 8 (144 + S))
    (hno : NewobjectC Heap (label "type__" + @NOTY@).toBitVec 24 (144 + S))
    (hlu : LuURejShortC S) (hfe : FmtErrorfWC Heap @FMT@ RO MsgIn (144 + S)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩'''

ITM_MAIN_PRE = '''  have hT4 : 4 ≤ T := by omega
  have ho4 : (tl.take 4).length = 4 := by simp; omega
  have hoff : Int.ofBytes (tl.take 4) = ((4 * n : Nat) : Int) := by
    rw [hfirst, ofBytes_uintBytes4 _ (by omega)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *'''

ITM_MAIN_TAIL = '''  have hrcx4 : 4 ≤ rcx.toNat := by omega
  have hrdi4 : 4 ≤ rdi.toNat := by omega
  rw [lca_m4 _ (by simpa using hrdi4), lca_m4' _ (by simpa using hrcx4), BitVec.mul_one,
    show rcx.toBitVec.toNat - 4 = T by simp; omega] at N11
  rw [show Int.toBytes 8 rdi.toBitVec.toInt = Int.toBytes 8 (BitVec.ofNat 64 rdi.toBitVec.toNat).toInt by simp] at N11
  have htl : Eq (tl.At (rbx.toBitVec + 4)) = Eq ((tl.take 4).At (rbx.toBitVec + 4))
      ⋆ Eq ((tl.drop 4).At (rbx.toBitVec + 4 + 4)) := by
    conv => lhs; rw [← List.take_append_drop 4 tl]
    exact at_app _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; rfl) (by simp; omega)
  refine eventually_trans _ _ _ _ (lcl_itemerr k hk hf rsp.toBitVec (rbx.toBitVec + 4) rax.toBitVec rax1.toBitVec tl []
    T n 0 (4 * n) T hT hn (by omega) (by omega) rfl (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _) (fun _ => rfl)
    hT32 rdi.toBitVec.toNat (by simp; omega) (by simpa using hcap63) S hS stk1
    (Int.toBytes 8 (Host.addrOf (k + @MSCALL@ + 1)).toBitVec.toInt) (sm1.take 8) ((sm1.drop 8).take 8) ((sm1.drop 8).drop 8)
    l200 l192 l136 (Int.toBytes 8 (BitVec.ofNat 64 (4 * n)).toInt) l160 l184 b0
    hstk1 (Int.toBytes_length 8 _) (by simp [hsm1]) (by simp [hsm1]) (by simp [hsm1]) hl200 hl192 hl136
    (Int.toBytes_length 8 _) hl160 hl184 hb0 ra rbp guard e0 e1 ity msg hm sp hity he0 hit RO MsgIn hmsg
    Heap (avail - 8 * n) (by omega)
    (Eq ((Int.toBytes 8 rbx.toBitVec.toInt).At (rsp.toBitVec + 16)) ⋆ Eq ([4, 0, 0, 0].At rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (rax.toBitVec + 16))) R _
    (by simp) (by show (BitVec.ofNat 64 n).toNat = _; simp; omega)
    (by show (BitVec.ofNat 64 (4 * n)).toNat = _; simp; omega)
    (by simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega) hguard hsp
    (by
      dsimp only
      simp only [List.nil_append, Nat.sub_zero]
      rw [htl]
      ecancel) hno hlu hfe) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrsp2, hrbp2, Hm2⟩
  dsimp only at hpc2 hrax2 hrsp2 hrbp2 Hm2
  refine Eventually.done _ ⟨hpc2, hrax2, ?_, hrbp2, Hm2⟩
  apply UInt64.toBitVec_inj.mp; rw [hrsp2]; simp'''
