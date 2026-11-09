# Witness generators

Regenerate every generated `Fk/Wit*.lean` (from `fv/kraken/lean`): `python3 tools/wit/wgen.py`.

| File | Generator | Theorem |
| --- | --- | --- |
| WitAdM | `wadm.py 3` | `ad_marshal_runs` |
| WitBl1 | `wbl.py 1` | `bl_accept_runs` |
| WitBl257 | `wbl.py 257` | `bl_accept_runs` |
| WitBlM1 | `wblm.py 1` | `bl_marshal_runs` |
| WitBlM257 | `wblm.py 257` | `bl_marshal_runs` |
| WitBlR | `wblr.py` | `bl_marshal_reject_runs` |
| WitBlRI | `wblri.py` | `bl_reject_invalid_runs` |
| WitBv | `wbv.py` | `bv_accept_runs` |
| WitBvM | `wmar.py bv` | `bv_marshal_runs` |
| WitBvR | `wbvr.py` | `bv_reject_padding_runs` |
| WitCpMR | `wmrej.py cp` | `cp_marshal_reject_runs` |
| WitFvM | `wmar.py fv` | `fv_marshal_runs` |
| WitFvMR | `wmrej.py fv` | `fv_marshal_reject_runs` |
| WitLcA1 | `wlca.py 1` | `lc_accept_runs` |
| WitLcA1x1 | `wlca.py 1 1x1` | `lc_accept_runs` |
| WitLcA4 | `wlca.py 4` | `lc_accept_runs` |
| WitLcA4x16 | `wlca.py 16,16,16,16 4x16` | `lc_accept_runs` |
| WitLcAMix | `wlca.py 0,1,16 Mix` | `lc_accept_runs` |
| WitLcE | `wlce.py` | `lc_accept_empty_runs` |
| WitLcI | `wlci.py` | `lc_reject_item_runs` |
| WitLcO | `wlco.py` | `lc_reject_order_runs` (정적 표는 항목 4·8만 놓는다. 표 레이블은 스택·수신자·입력 버퍼 뒤) |
| WitLcM0 | `wlcm.py 0` | `lc_marshal_runs` |
| WitLcM1 | `wlcm.py 1` | `lc_marshal_runs` |
| WitLcM1x1 | `wlcm.py 1 1x1` | `lc_marshal_runs` |
| WitLcM4 | `wlcm.py 4` | `lc_marshal_runs` |
| WitLcM4x16 | `wlcm.py 16,16,16,16 4x16` | `lc_marshal_runs` |
| WitLcMMix | `wlcm.py 0,1,16 Mix` | `lc_marshal_runs` |
| WitLcP | `wlcz.py past` | `lc_reject_past_runs` |
| WitLcS0 | `wlcs.py 0` | `lc_size_runs` |
| WitLcS1 | `wlcs.py 1` | `lc_size_runs` |
| WitLcS4 | `wlcs.py 4` | `lc_size_runs` |
| WitLcT | `wlcz.py tail` | `lc_reject_tail_runs` |
| WitLcZ | `wlcz.py zero` | `lc_reject_zero_runs` |
| WitLuComp | `wcomp.py` | `lu_compose_runs` |
| WitLuG | `wlug.py` | `lum_grow_runs` |
| WitLuM0 | `wmar.py lu0` | `lu_marshal_runs` |
| WitLuM1 | `wmar.py lu1` | `lu_marshal_runs` |
| WitLuM16 | `wmar.py lu16` | `lu_marshal_runs` |
| WitLuMR | `wmrej.py lu` | `lu_marshal_reject_runs` |
| WitLuMa | `wlur.py misaligned` | `lu_reject_misaligned_runs` |
| WitLuTb | `wlur.py toobig` | `lu_reject_toobig_runs` |
| WitNe0 | `wne.py 0` | `ne_accept_runs` |
| WitNe1 | `wne.py 1` | `ne_accept_runs` |
| WitNe16 | `wne.py 16` | `ne_accept_runs` |
| WitNeM0 | `wnem.py 0` | `ne_marshal_runs` |
| WitNeM1 | `wnem.py 1` | `ne_marshal_runs` |
| WitNeM16 | `wnem.py 16` | `ne_marshal_runs` |
| WitNeS0 | `wnes.py 0` | `ne_size_runs` |
| WitNeS1 | `wnes.py 1` | `ne_size_runs` |
| WitNeS16 | `wnes.py 16` | `ne_size_runs` |
| WitRjAdSz | `wrej.py` | `ad_reject_size_runs` |
| WitRjBlOf | `wrej.py` | `bl_reject_offset_runs` |
| WitRjBlSh | `wrej.py` | `bl_reject_short_runs` |
| WitRjBvSz | `wrej.py` | `bv_reject_size_runs` |
| WitRjCpSz | `wrej.py` | `cp_reject_size_runs` |
| WitRjFvSz | `wrej.py` | `fv_reject_size_runs` |
| WitRjLcOf | `wrej.py` | `lc_reject_offset_runs` |
| WitRjLcSh | `wrej.py` | `lc_reject_short_runs` |
| WitRjLuOf | `wrej.py` | `lu_reject_offset_runs` |
| WitRjLuSh | `wrej.py` | `lu_reject_short_runs` |
| WitRjNeOf | `wrej.py` | `ne_reject_offset_runs` |
| WitRjNeSh | `wrej.py` | `ne_reject_short_runs` |
| WitRjScSz | `wrej.py` | `sc_reject_size_runs` |
| WitScA | `wacc.py sc` | `sc_accept_runs` |
| WitScComp | `wcompsc.py` | `sc_compose_runs` |
| WitScM | `wmar.py sc` | `sc_marshal_runs` |
| WitScRB | `wscrb.py` | `sc_reject_bool_runs` |
| WitSzAd | `wsize.py` | `ad_size_runs` |
| WitSzBl | `wsize.py` | `bl_size_runs` |
| WitSzBv | `wsize.py` | `bv_size_runs` |
| WitSzCp | `wsize.py` | `cp_size_runs` |
| WitSzFv | `wsize.py` | `fv_size_runs` |
| WitSzLu | `wsize.py` | `lu_size_runs` |
| WitSzSc | `wsize.py` | `sc_size_runs` |
| WitVbv | `wacc.py vbv` | `vbv_accept_runs` |
| WitVbvR | `wvbvr.py` | `vbv_reject_pad_runs` |
| WitAd | none (the file is the record) | `ad_accept_runs` |
| WitCp | none (the file is the record) | `cp_accept_runs` |
| WitCpM | none (the file is the record) | `cp_marshal_runs` |
| WitFv | none (the file is the record) | `fv_accept_runs` |
| Witness | none (hand-written) | `growslice_call_runs` |

Go value check: `go run fv/kraken/lean/tools/wit/layout.go > fv/kraken/lean/tools/wit/layout.json` (from the repository root), then `python3 tools/wit/goval.py`.
