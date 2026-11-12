import E2eDec.SpecA
import E2eDec.StmtCompS
import E2eEnc.Fast

/-!
# Round trip (machine): decoder entry → `dcd_e2e_accept_main` → (caller: `hupd`) → `dc_e2e_marshal_fast_main`

The order of `Prysm.Checkpoint.DecodeThenEncode.round_trip` (`Prysm/Checkpoint/DecodeThenEncode.lean`). Statement: the corrected
`dc_unmarshal_then_marshal_s_stmt` (`StmtCompS.lean`, the frozen text plus `S < 2^60`). Frame mapping (x = rsp at both entries):
the decoder leaves the saved rbp at x − 8 and the rax/rbx spills at x + 8, x + 16; these are the encoder's `fp`, `s1`,
`s2`. The encoder slots x − 24, x − 32, x − 40, x − 56, x − 64 are the caller's `g24 … g64`. The encoder's return slot
x − 144 is the first word of the decoder's callee spill area; its scratch (`S + 8` bytes at x − 152 − S) is the
decoder's scratch and the decoder's runtime-call return slot. The receiver words that the decoder wrote are the
encoder's receiver premises with `nb = BitVec.ofNat 64 n`.
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz E2eDec.Code E2eEnc
variable [Host]

namespace E2eDec

theorem dcc_scr (x : BitVec 64) (S : Nat) (hS : S + 8 < 2 ^ 64) (lo ret : List UInt8) (hlo : lo.length = S)
    (hret : ret.length = 8) :
    Eq ((lo ++ ret).At (x - 144 - BitVec.ofNat 64 (S + 8))) =
      Eq (lo.At (x - 152 - BitVec.ofNat 64 S)) ⋆ Eq (ret.At (x - 152)) := by
  have e : x - 144 - BitVec.ofNat 64 (S + 8) = x - 152 - BitVec.ofNat 64 S := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [e, at_app lo ret (b := x - 152) (by rw [hlo]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega)
    (by simp [hlo, hret]; omega)]

theorem dcc_spl (x : BitVec 64) (spl : List UInt8) (h : spl.length = 40) :
    Eq (spl.At (x - 144)) = Eq ((spl.take 8).At (x - 144)) ⋆ Eq ((spl.drop 8).At (x - 136)) := by
  conv => lhs; rw [← List.take_append_drop 8 spl]
  exact at_app _ _ (by rw [List.length_take, h]; bv_omega) (by simp [h])

theorem dc_e2e_unmarshal_then_marshal_s : dc_unmarshal_then_marshal_s_stmt := by
  intro k hk hf km hkm hfm n hn root ib hroot hib s ra ra2 guard fp s1 s2 s3 s4 l28 l30 l38 l40 spl rslot lo
    aP1 aL1 aC1 aP2 aL2 aC2 hfp h1 h2 h3 h4 hl28 hl30 hl38 hl40 hspl hrs haP1 haL1 haC1 haP2 haL2 haC2
    g24 g32 g40 g56 g64 pre d hg24 hg32 hg40 hg56 hg64 hd dptr dlen cap hpre hcap2 S hS hlo R Heap avail h_mem
    hguard hlen hcap hcap63 hav hms hmsU hmm hmm2
  refine eventually_trans _ _ _ _ (dcd_e2e_accept_main k hk hf n hn root ib hroot hib s ra guard fp s1 s2 s3 s4 l28
    l30 l38 l40 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2 hfp h1 h2 h3 h4 hl28 hl30 hl38 hl40 hspl hrs haP1 haL1 haC1
    haP2 haL2 haC2 S hlo _ Heap avail h_mem hguard hlen hcap hcap63 hav hms hmsU hmm) ?_
  rintro ⟨dd, pc⟩ ⟨hpc, hrax, hrbx, hrsp, hrbp, hr14, pb, A, l28', l30', l38', l40', spl', lo', -, -, -, -, hspl',
    hlo', hm⟩
  refine Eventually.done _ ⟨hpc, hrax, hrbx, fun mem2 zm fl hupd => ?_⟩
  rw [dcc_spl _ spl' hspl'] at hm
  have hmem2 := hupd _ (by ecancel)
  refine eventually_trans _ _ _ _ (dc_e2e_marshal_fast_main km hkm hfm _ ra2 guard pb A (BitVec.ofNat 64 n) n
    (by simp; omega) hn root ib pre d hroot hib (by dsimp only; exact hpre) hd
    (Int.toBytes 8 s.regs.rbp.toBitVec.toInt) (Int.toBytes 8 s.regs.rax.toBitVec.toInt)
    (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) g24 g32 g40 g56 g64 (spl'.take 8)
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) hg24 hg32 hg40 hg56 hg64
    (by simp [hspl']) (S + 8) (lo' ++ Int.toBytes 8 (Host.addrOf (k + 76)).toBitVec.toInt)
    (by simp [hlo', Int.toBytes_length]) _
    (by
      dsimp only
      rw [hr14, dcc_scr _ S (by omega) lo' _ hlo' (Int.toBytes_length 8 _)]
      ecancel)
    (by dsimp only; omega) (by dsimp only; omega) hmm2) ?_
  intro st' hh
  obtain ⟨e1, e2, e3, e4, e5, e6, -, -, -, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm'⟩ := hh
  dsimp only at e2 e3 e4 hm'
  refine Eventually.done _ ⟨e1, e2, e3, e4, e5, e6, ?_⟩
  rw [show pre ++ (root ++ dcOff ++ ib) = pre ++ root ++ dcOff ++ ib by simp,
    dcd_in_split _ _ _ hroot (by rw [hib]; omega)]
  exact sep_true (by ecancel)

end E2eDec
