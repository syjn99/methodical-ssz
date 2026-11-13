import Runtime.Contracts
import Machine.Step
import Prysm.DataColumnsByRootIdentifier.SpecDefinitions
import Prysm.DataColumnsByRootIdentifier.EncodeLoop

/-!
# From `L_7c` (directive 29) to the return, sites 2 and 3 do not grow

Shared by the fast path (`Encode.fast_path`, from directive 15 `jae L_7c`) and the grow path at site 1
(`Encode.grow_first_site`, after the growslice of directive 23). At `L_7c` the block is `bp` with capacity `cp`,
rcx = len, r8 = len + 32, rdx = the BlockRoot pointer `pr`, rsp = x − 136.

30–32 spill r8, rbx, rdi to x − 64, x − 32, x − 56; 33–36 `memmove(bp + len, pr, 32)`; 37–42 `len + 36 ≤ cp`, so
the `jb` to the growslice of site 2 is not taken; 43–44 `jmp L_cd`; 51 `movl $0x24,-0x4(%rbx,%rax,1)` (the offset 36
at bp + len + 32); 52–55 n from c + 40, `jg` not taken (n ≤ 128); 56–60 n and the Columns pointer to x − 40, x − 24,
rsi = 0, `jmp L_13a`; the loop (`Encode.loop`); 100–105 rdi = rsi = 0, epilogue, `ret`.
-/

open Machine Runtime Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

omit [Host] in
/-- `cmp $0x80, a; jg` is not taken when `a ≤ 128` (the text of `Prysm.IndexedAttestation.Decode.jg2048_false`). -/
theorem Encode.jg128_false (a : BitVec 64) (af : Bool) (h : a.toNat ≤ 128) :
    CondCode.g.interp (StatusFlags.from_result (a - 128)
      { cf := BitVec.unsigned (a - 128) != a.unsigned - BitVec.unsigned (128 : BitVec 64), af := af,
        of := BitVec.toInt (a - 128) != a.toInt - BitVec.toInt (128 : BitVec 64) }) = false := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have t16 : BitVec.toInt (128 : BitVec 64) = 128 := by decide
  have hs : (a - 128).toInt = (a.toNat : Int) - 128 := by
    rw [BitVec.toInt_sub, ta, t16]; apply Int.bmod_eq_of_le <;> omega
  by_cases h16 : a.toNat = 128
  · have : a - 128 = 0#64 := by apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
    simp [CondCode.interp, StatusFlags.from_result]
    intro h1; exact absurd this h1
  · have hm : (a - 128).msb = true := by
      rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
    simp [CondCode.interp, StatusFlags.from_result, ta]
    intro _
    rw [show (a - 128#64).msb = true from hm, Int.bmod_eq_of_le (by omega) (by omega)]; simp

omit [Host] in
theorem Encode.tail_split (d : List UInt8) (n : Nat) (hd : d.length = 36 + 8 * n) (hn : n ≤ 128) (a : BitVec 64) :
    Eq (d.At a) = Eq ((d.take 32).At a) ⋆ Eq (((d.drop 32).take 4).At (a + 32)) ⋆ Eq ((d.drop 36).At (a + 36)) := by
  have e1 : d = d.take 32 ++ ((d.drop 32).take 4 ++ d.drop 36) := by
    rw [show 36 = 32 + 4 from rfl, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  conv => lhs; rw [e1]
  rw [Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
    ← Std.ExtHashMap.sep_assoc]
  have l1 : (d.take 32).length = 32 := by simp; omega
  have l2 : ((d.drop 32).take 4).length = 4 := by simp; omega
  rw [l1, l2, show a + BitVec.ofNat 64 32 + BitVec.ofNat 64 4 = a + 36 by bv_omega]; rfl

omit [Host] in
theorem Encode.tail_join (root cb : List UInt8) (n : Nat) (hroot : root.length = 32) (hcb : cb.length = 8 * n)
    (hn : n ≤ 128) (a : BitVec 64) :
    Eq (root.At a) ⋆ Eq (offsetBytes.At (a + 32)) ⋆ Eq (cb.At (a + 36)) = Eq ((root ++ offsetBytes ++ cb).At a) := by
  rw [List.append_assoc, Mem.At_append_sep _ _ _ (by simp [offsetBytes]; omega),
    Mem.At_append_sep _ _ _ (by simp [offsetBytes]; omega), ← Std.ExtHashMap.sep_assoc, hroot,
    show offsetBytes.length = 4 from rfl, show a + BitVec.ofNat 64 32 + BitVec.ofNat 64 4 = a + 36 by bv_omega]; rfl

omit [Host] in
theorem Encode.tail_offset_addr (x y z : BitVec 64) (h : y = z + 32) : 4 + y + x * 1#64 + -4 = x + z + 32 := by
  subst h; bv_omega

omit [Host] in
theorem Encode.tail_room (y z w : BitVec 64) (cp : Nat) (h : y = z + 32) (hw : w.toNat = cp) (hc : z.toNat + 36 ≤ cp)
    (hc64 : cp < 2 ^ 64) : (4 + y).toNat ≤ w.toNat := by
  subst h; simp [BitVec.toNat_add]; omega

omit [Host] in
theorem Encode.offset_bytes_eq : Int.toBytes 4 (BitVec.truncate 32 (36 : BitVec 64)).toInt = offsetBytes := by decide

omit [Host] in
theorem Encode.tail_l36 (x : BitVec 64) (z : UInt64) (hz : z.toNat + 36 < 2 ^ 64) :
    x + BitVec.ofNat 64 (z.toNat + 36) = x + z.toBitVec + 36 := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

omit [Host] in
theorem Encode.tail_rbx36 (y z : BitVec 64) (h : y = z + 32) (hz : z.toNat + 36 < 2 ^ 64) :
    (4 + y).toNat = z.toNat + 36 + 8 * 0 := by
  subst h; simp [BitVec.toNat_add]; omega

theorem Encode.tail_fit (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (x c pr pc nb bp : BitVec 64) (ra ob : UInt64) (n cp : Nat) (hnb : nb.toNat = n) (hn : n ≤ 128)
    (root cb d : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 8 * n) (hd : d.length = 36 + 8 * n)
    (l24 l32 l40 l56 l64 rslot : List UInt8) (hl24 : l24.length = 8) (hl32 : l32.length = 8)
    (hl40 : l40.length = 8) (hl56 : l56.length = 8) (hl64 : l64.length = 8) (hrs : rslot.length = 8)
    (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S) (R : DataMem → Prop) (s : MachineData)
    (hrsp : s.regs.rsp.toBitVec = x - 136) (hrbx : s.regs.rbx.toBitVec = bp) (hrdi : s.regs.rdi.toNat = cp)
    (hr8 : s.regs.r8.toBitVec = s.regs.rcx.toBitVec + 32) (hrdx : s.regs.rdx.toBitVec = pr)
    (hcp : s.regs.rcx.toNat + 36 + 8 * n ≤ cp)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 ob.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 c.toInt).At (x + 8))
      ⋆ Eq (l24.At (x - 24)) ⋆ Eq (l32.At (x - 32)) ⋆ Eq (l40.At (x - 40)) ⋆ Eq (l56.At (x - 56))
      ⋆ Eq (l64.At (x - 64)) ⋆ Eq (rslot.At (x - 144)) ⋆ Eq (scratch.At (x - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 pc.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
      ⋆ Eq (root.At pr) ⋆ Eq (cb.At pc) ⋆ Eq (d.At (bp + s.regs.rcx.toBitVec)) ⋆ R)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toBitVec = bp
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 36 + 8 * n ∧ st.data.regs.rcx.toNat = cp
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp.toBitVec = x + 8 ∧ st.data.regs.rbp = ob ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (l24' l32' l40' l56' l64' rslot' scr : List UInt8), l24'.length = 8 ∧ l32'.length = 8 ∧ l40'.length = 8
          ∧ l56'.length = 8 ∧ l64'.length = 8 ∧ rslot'.length = 8 ∧ scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 ob.toBitVec.toInt).At (x - 8))
          ⋆ Eq ((Int.toBytes 8 c.toInt).At (x + 8))
          ⋆ Eq (l24'.At (x - 24)) ⋆ Eq (l32'.At (x - 32)) ⋆ Eq (l40'.At (x - 40)) ⋆ Eq (l56'.At (x - 56))
          ⋆ Eq (l64'.At (x - 64)) ⋆ Eq (rslot'.At (x - 144)) ⋆ Eq (scr.At (x - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 pc.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
          ⋆ Eq (root.At pr) ⋆ Eq (cb.At pc) ⋆ Eq ((root ++ offsetBytes ++ cb).At (bp + s.regs.rcx.toBitVec)) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 29)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, ⟨rspb⟩, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrsp hrbx hrdi hr8 hrdx hcp ⊢
  subst hrsp hrbx hrdx
  have hz1 := rcx.toNat_lt_size; have hz2 := rdi.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2
  rw [Encode.tail_split d n hd hn] at h_mem
  kat hk marshalSSZTo 29
  kat hk marshalSSZTo 30
  apply store_step_at _ _ (x - 64) _ _ _ l64 _ _ (by daddr) (by ecancel) (by exact hl64)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk marshalSSZTo 31
  apply store_step_at _ _ (x - 32) _ _ _ l32 _ _ (by daddr) (by ecancel) (by exact hl32)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk marshalSSZTo 32
  apply store_step_at _ _ (x - 56) _ _ _ l56 _ _ (by daddr) (by ecancel) (by exact hl56)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk marshalSSZTo 33
  kat hk marshalSSZTo 34
  kat hk marshalSSZTo 35
  kat hk marshalSSZTo 36
  apply store_step_at _ _ (x - 144) _ _ _ rslot _ _ (by daddr) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  rw [BitVec.mul_one, show x - 136 - 8#64 = x - 144 by bv_omega]
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 36 + 1)) root (d.take 32) scratch _
    (by rw [hroot]; rfl) (by simp [hd, hroot]; omega) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  simp only at hrsp1 hr141 hrbp1 Hm1
  have hrsp1' : rsp1 = { toBitVec := x - 136 } := by
    rw [hrsp1]; apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  subst hrsp1' hr141 hrbp1
  kat hk marshalSSZTo 37
  apply load_step_at _ _ (x - 64) _ _ (Int.toBytes 8 r8.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 38
  kat hk marshalSSZTo 39
  kat hk marshalSSZTo 40
  apply load_step_at _ _ (x - 56) _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 41
  kat hk marshalSSZTo 42
  split
  case isTrue h =>
    exfalso; simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    have := Encode.tail_room r8.toBitVec rcx.toBitVec rdi.toBitVec cp hr8 hrdi (Nat.le_trans (Nat.le_add_right _ _) hcp)
      (by omega)
    simp [BitVec.toNat_add] at this h; omega
  simp only [Effects.All]
  kat hk marshalSSZTo 43
  apply load_step_at _ _ (x - 32) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 44
  klabel hk hf marshalSSZTo 50
  kat hk marshalSSZTo 50
  kat hk marshalSSZTo 51
  rw [Encode.tail_offset_addr _ _ _ hr8]
  apply store_step _ _ _ _ _ ((d.drop 32).take 4) _ _ (by ecancel) (by simp; omega)

  intro m5 H5
  simp only [Width.bytes, Encode.offset_bytes_eq] at H5
  kunfold
  kat hk marshalSSZTo 52
  apply load_step_at _ _ (x + 8) _ _ (Int.toBytes 8 c.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 53
  apply load_step_at _ _ (c + 40) _ _ (Int.toBytes 8 nb.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 54
  kat hk marshalSSZTo 55
  split
  case isTrue h => exfalso; rw [Encode.jg128_false _ _ (by omega)] at h; exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk marshalSSZTo 56
  apply store_step_at _ _ (x - 40) _ _ _ l40 _ _ (by daddr) (by ecancel) (by exact hl40)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk marshalSSZTo 57
  apply load_step_at _ _ (c + 32) _ _ (Int.toBytes 8 pc.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 58
  apply store_step_at _ _ (x - 24) _ _ _ l24 _ _ (by daddr) (by ecancel) (by exact hl24)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk marshalSSZTo 59
  intro _
  kat hk marshalSSZTo 60
  klabel hk hf marshalSSZTo 82
  have hb36 : rcx.toNat + 36 < 2 ^ 64 := by omega
  refine eventually_trans _ _ _ _ (Encode.loop k hk hf cb (d.drop 36) n (rcx.toNat + 36) cp hcb (by simp [hd]) hn
    (by omega) (by omega) rbx.toBitVec pc _ _ _ _ n 0 _ (by omega) rfl (Encode.tail_rbx36 _ _ hr8 hb36) (by simpa using hrdi)
    rfl (by simp) (by simpa [hnb] using hnb) rfl rfl rfl
    (by simp only [Nat.mul_zero, List.take_zero, List.drop_zero, List.nil_append]
        rw [Encode.tail_l36 _ _ hb36]
        ecancel)) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrcx2, hrsp2, hrbp2, hr142, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrcx2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := e2
  simp only at hrax2 hrbx2 hrcx2 hrsp2 hrbp2 hr142 Hm2
  subst hrsp2 hrbp2 hr142
  rw [Encode.tail_l36 _ _ hb36] at Hm2
  kat hk marshalSSZTo 100
  kat hk marshalSSZTo 101
  intro _
  kat hk marshalSSZTo 102
  intro _
  kat hk marshalSSZTo 103
  kat hk marshalSSZTo 104
  apply load_step_at _ _ (x - 8) _ _ (Int.toBytes 8 ob.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 105
  apply load_step_at _ _ x _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Int.toBytes 8 pc.toInt, Int.toBytes 8 rbx.toBitVec.toInt,
    Int.toBytes 8 nb.toInt, Int.toBytes 8 rdi.toBitVec.toInt, Int.toBytes 8 r8.toBitVec.toInt,
    Int.toBytes 8 (Host.addrOf (k + 36 + 1)).toBitVec.toInt, stk1, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, hstk1, ?mem⟩
  case mem =>
    rw [← Encode.tail_join root cb n hroot hcb hn]
    ecancel
  all_goals first
    | trivial
    | rfl
    | exact hrax2
    | exact hrcx2
    | exact hrbx2
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | daddr

end Prysm.DataColumnsByRootIdentifier
