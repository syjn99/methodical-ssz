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
