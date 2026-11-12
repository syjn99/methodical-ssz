import E2eEnc.Grow
import E2eEnc.Spec
import Fk.RtCopy

/-!
# Grow path at site 1 against EthLib (`dc_marshal_grow_spec_stmt`)

From `dc_e2e_marshal_grow_main`: the new block starts with `pre ‖ serialize prysmDcDesc g.toValue`.
-/

open Fk E2eEnc.Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eEnc

theorem dc_e2e_marshal_grow_spec : dc_marshal_grow_spec_stmt := by
  intro k hk hf s ra guard pr pc nb g hnb pre hpre fp s1 s2 s3 l16 l24 l32 l40 l56 l64 spl rslot hfp h1 h2 h3 hl16
    hl24 hl32 hl40 hl56 hl64 hspl hrs S scratch hsc Heap avail R h_mem hguard hlc hgrow hfit hbud hmax hgs hmm
  refine ⟨pdcEnc g, pdc_serialize g, ?_⟩
  have hroot : g.root.toList.length = 32 := by simp
  have hcb : (Fv1.u64Bytes g.cols).toList.length = 8 * g.cols.length := by simp [Fv1.u64Bytes_size]
  refine eventually_mono (dc_e2e_marshal_grow_main k hk hf s ra guard pr pc nb g.cols.length hnb g.hcols _ _ pre
    hroot hcb hpre fp s1 s2 s3 l16 l24 l32 l40 l56 l64 spl rslot hfp h1 h2 h3 hl16 hl24 hl32 hl40 hl56 hl64 hspl hrs
    S scratch hsc Heap avail R h_mem hguard hlc hgrow hfit hbud hmax hgs hmm) ?_
  rintro st ⟨hpc, hrbx, hnc, hrdi, hrsi, -, -, -, _, _, _, _, _, _, _, _, _, rest, _, _, _, _, _, _, _, _, _, _,
    hrest, _, hm⟩
  refine ⟨hpc, by rw [hrbx, pdc_enc_size]; omega, by rw [pdc_enc_size]; omega, hrdi, hrsi, ?_⟩
  rw [pdc_enc_toList, show pre ++ (g.root.toList ++ dcOff ++ (Fv1.u64Bytes g.cols).toList)
    = pre ++ g.root.toList ++ dcOff ++ (Fv1.u64Bytes g.cols).toList by simp]
  have hl : (pre ++ g.root.toList ++ dcOff ++ (Fv1.u64Bytes g.cols).toList).length + rest.length ≤ 2 ^ 64 := by
    have := st.data.regs.rcx.toNat_lt_size; simp only [UInt64.size] at this
    simp [hpre, dcOff, Fv1.u64Bytes_size] at hrest ⊢; omega
  rw [Mem.At_append_sep _ rest _ hl] at hm
  exact sep_true (by ecancel)

end E2eEnc
