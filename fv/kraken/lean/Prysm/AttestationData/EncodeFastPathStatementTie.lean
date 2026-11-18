import Prysm.AttestationData.EncodeFastPath
import Prysm.AttestationData.GeneratedEncodeFastPath

/-!
# Tie of the generated encoder fast-path theorem of `AttestationData` to the hand theorem

`Encode.fast_path_statement_tie` shows that the generated theorem `Encode.generated_fast` implies the statement of the
hand theorem `Encode.fast_path`.
`Encode.fast_path_implies_generated_fast` shows the reverse implication.
So the two statements are equivalent.
The ties of Deposit_Data, PowBlock and SyncCommitteeMessage are identities by `rfl`.
This tie is not an identity, so it has two implications.
The statements differ in three points only.
The names and the order of the binders and of the memory chunks differ.
The hand post-state names the 128 output bytes as one chunk, and the generated post-state names one chunk per SSZ leaf.
The hand post-state writes the word at rsp − 224 as `rcx + 48 + 40 + 40`, and the generated post-state as `rcx + 128`.
-/

open Machine Runtime Codec

namespace Prysm.AttestationData
variable [Host]

/-- **The generated theorem implies the hand statement** `Encode.fast_path`. -/
theorem Encode.fast_path_statement_tie : type_of% (@Prysm.AttestationData.Encode.fast_path ‹Host›) := by
  intro k hk hf kC hkC hfC S hS hmm s ra guard rp ps pt p1 p2 hps hpt
    sl ix root cs e1 cC1 ctl1 root1 ct e2 cC2 ctl2 root2 pre d0 d1 d2 d3 d4 d5 d6
    hsl hix hroot hcs he1 hcC1 hctl1 hroot1 hct he2 hcC2 hctl2 hroot2 hpre hd0 hd1 hd2 hd3 hd4 hd5 hd6
    fp a8 b16 ta tb tc td q48 q120 q128 q176 rslot lo hfp ha8 hb16 hta htb htc htd h48 h120 h128 h176 hrs hlo
    R h_mem hguard hcap hcap63
  refine eventually_mono (Encode.generated_fast k hk hf kC hkC hfC sl ix root e1 root1 e2 root2 cs cC1 ctl1 ct cC2 ctl2
    pre d0 d1 d2 d3 d4 d5 d6 hsl hix hroot he1 hroot1 he2 hroot2 hcs hcC1 hctl1 hct hcC2 hctl2 hd0 hd1 hd2 hd3 hd4 hd5 hd6
    rp ps p1 pt p2 hps hpt s ra guard hpre fp a8 b16 ta tb tc td q48 q120 q128 q176 rslot hfp ha8 hb16 hta htb htc htd
    h48 h120 h128 h176 hrs R S hS lo hlo (by ecancel) hguard hcap hcap63 hmm) ?_
  rintro st ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, x0, x1, x2, x3, x4, x5, x6, x7, x8,
    hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hm⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, x0, x1, x2, x3, x6, x5, x8, x7, x4,
    hx0, hx1, hx2, hx3, hx6, hx5, hx8, hx7, hx4, ?_⟩
  rw [Encode.merge_encoding sl ix root e1 root1 e2 root2 _ hsl hix hroot he1 hroot1 he2 hroot2,
    show s.regs.rcx.toBitVec + 48 + 40 + 40 = s.regs.rcx.toBitVec + 128 by bv_omega,
    show s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8 = s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8 from rfl]
  rw [show s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16 = s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16 from rfl]
  ecancel

/-- **The hand theorem implies the generated statement** `Encode.generated_fast`. -/
theorem Encode.fast_path_implies_generated_fast : type_of% (@Prysm.AttestationData.Encode.generated_fast ‹Host›) := by
  intro k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4
    hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64
    t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc
    h_mem hguard hcap hcap63 hmm
  refine eventually_mono (Encode.fast_path k hk hf kC hkC hfC S hS hmm s ra guard p2 p3 p4 pr3 pr4 hp3 hp4
    v0 v1 b2 ob3 ep3 oc3 ot3 rt3 ob4 ep4 oc4 ot4 rt4 pre d0 d1 d2 d3 dr3 d4 dr4
    hv0 hv1 hb2 hob3 hep3 hoc3 hot3 hrt3 hob4 hep4 hoc4 hot4 hrt4 hpre hd0 hd1 hd2 hd3 hdr3 hd4 hdr4
    fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot scratch hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot hsc
    R (by ecancel) hguard hcap hcap63) ?_
  rintro st ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, t1, u1, t2, u2, t, u, scr, rs', gap,
    ht1, hu1, ht2, hu2, ht, hu, hscr, hrs', hgap, hm⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, t1, u1, t2, u2, gap, u, t, rs', scr,
    ht1, hu1, ht2, hu2, hgap, hu, ht, hrs', hscr, ?_⟩
  rw [Encode.merge_encoding v0 v1 b2 ep3 rt3 ep4 rt4 _ hv0 hv1 hb2 hep3 hrt3 hep4 hrt4,
    show s.regs.rcx.toBitVec + 48 + 40 + 40 = s.regs.rcx.toBitVec + 128 by bv_omega] at hm
  ecancel

end Prysm.AttestationData
