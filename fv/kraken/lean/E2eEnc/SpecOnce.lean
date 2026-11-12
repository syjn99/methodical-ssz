import E2eEnc.Once
import E2eEnc.Spec

/-!
# ENC G1* against EthLib (`dc_marshal_once_spec_stmt`)

From `dc_e2e_marshal_once_main`: the result block starts with `pre ‖ serialize prysmDcDesc g.toValue`.
-/

open Fk E2eEnc.Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eEnc

theorem dc_e2e_marshal_once_spec : dc_marshal_once_spec_stmt := by
  intro k hk hf s ra guard pr pc nb g hnb pre spare hpre hspare fp s1 s2 s3 l16 l24 l32 l40 l48 l56 l64 l72 spl rslot
    hfp h1 h2 h3 hl16 hl24 hl32 hl40 hl48 hl56 hl64 hl72 hspl hrs S scratch hsc Heap avail R h_mem hguard hbud hone hmax
    hgs hmm
  refine ⟨pdcEnc g, pdc_serialize g, ?_⟩
  have hroot : g.root.toList.length = 32 := by simp
  have hcb : (Fv1.u64Bytes g.cols).toList.length = 8 * g.cols.length := by simp [Fv1.u64Bytes_size]
  refine eventually_mono (dc_e2e_marshal_once_main k hk hf s ra guard pr pc nb g.cols.length hnb g.hcols _ _ pre spare
    hroot hcb hpre hspare fp s1 s2 s3 l16 l24 l32 l40 l48 l56 l64 l72 spl rslot hfp h1 h2 h3 hl16 hl24 hl32 hl40 hl48
    hl56 hl64 hl72 hspl hrs S scratch hsc Heap avail R h_mem hguard hbud hmax hone hgs hmm) ?_
  rintro st ⟨hpc, hrbx, hcap, hrdi, hrsi, -, -, -, _, _, _, _, _, _, _, _, _, _, _, _, rest, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, hrest, _, hm⟩
  refine ⟨hpc, by rw [hrbx, pdc_enc_size]; omega, by rw [pdc_enc_size]; omega, hrdi, hrsi, ?_⟩
  rw [pdc_enc_toList, show pre ++ (g.root.toList ++ dcOff ++ (Fv1.u64Bytes g.cols).toList)
    = pre ++ g.root.toList ++ dcOff ++ (Fv1.u64Bytes g.cols).toList by simp]
  have hl : (pre ++ g.root.toList ++ dcOff ++ (Fv1.u64Bytes g.cols).toList).length + rest.length ≤ 2 ^ 64 := by
    have := st.data.regs.rcx.toNat_lt_size; simp only [UInt64.size] at this
    simp [hpre, dcOff, Fv1.u64Bytes_size] at hrest ⊢; omega
  rw [Mem.At_append_sep _ rest _ hl] at hm
  exact sep_true (by ecancel)

end E2eEnc
