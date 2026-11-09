# gen/x4: 명세 문장과 증명의 생성 (X4)

Desc와 Go 배치에서 정리 문장을, 기계어 지시 목록에서 증명을 만든다.
대상은 Go 1.26.3 ELF의 수작업 타입이다. Prysm 타입과 Go 1.26.10에 대해서는 아무것도 주장하지 않는다.
게이트 1c 통과가 아니다.

## 1. 파일

| 파일 | 무엇 |
| --- | --- |
| `x4gen.py` | 생성기. Desc는 `gen1c/emit.accept`(검사기 결과, sha256, SPEC)로만 받는다. 출력은 `lean/Gen1cX4/<T>.lean`(라이브러리 `Gen1cX4`, `lakefile.toml` 끝의 블록) |
| `compare.py`, `pairs-*.json` | 문장 비교: `∀ [Host], <obl>_stmt`와 손 정리의 타입이 정의상 같은지(`isDefEq`, 투명도 all) |
| `negative.py` | 부정 시험: 기계어 한 줄을 바꾼 사본으로 지정 정리를 다시 돈다. 대조군은 바꾸지 않은 사본 |
| `run_checks.sh` | gate 안 검사 실행기: build, 비교, 공리, 부정 시험을 메모리 캡 아래 돌리고 첫 실패 코드로 끝난다(리뷰 r5 S4) |
| `lcacc.py`, `lcacc_tpl.py` | ListC 수용: 항목 루프와 두 수용 경로의 걷기, 그 손 글 틀(5절) |
| `anchor.py` | 축약 Prysm 타입(바이트 벡터·컨테이너 필드)의 고정 손 틀(6절). 손 모듈에서 틀을 생성 시점에 읽는다 |
| `verbatim.py` | 생성 정리의 전술 줄 중 손 증명 파일에 글자 그대로 있는 줄 수(INBOX 014 정직성 규칙) |
| `axioms.py` | `#print axioms`를 프로그램으로 판정(`propext`, `Classical.choice`, `Quot.sound`만) |
| `lean/Gen1cX4/Support.lean` | 생성 증명이 쓰는 보조정리(손으로 씀, 생성 아님) |
| `results/` | 커밋된 결과 |

## 2. 생성 규칙 (고정 크기, uint·bool 필드)

- 문장: 입력 조각 `b<i>`(SSZ 오프셋, 너비), 수신자 조각 `c<i>`(Go 오프셋, `gen/wit/src/layout.json`), 경로의 레이블 가설, 길이 가설, bool 값 가설.
- 증명: 지시 하나마다 `estep`·`kunfold`, 그리고 종류별 블록(스필 저장, 입력 적재, 수신자 저장, rip 적재, `cmp`, 조건 점프, `xor`, `retq`).
  조건 점프는 경로의 모드(수용, 길이 거부, bool 거부)에서 결과를 정하고, 불가능한 갈래를 조건 종류별 조각으로 닫는다.
- 무엇이 생성이고 무엇이 손 글인가(리뷰 r5 S2): 지시 하나마다의 단계(`estep`·`kunfold`·`kat`와 적재·저장 블록, 레이블 번호, 주소 식, 점프 결과)는 `.S` 지시 목록과 Desc·배치에서 만든다. 갈래를 닫는 조각과 마무리 조각은 손 증명의 글을 너비·가설 이름·번호만 바꿔 담은 것이다(`Fk/ScAccept.lean`, `Fk/ScRejectBool.lean`, `Fk/ScReject.lean`, `Fk/ScMarshal.lean`, `Fk/ComposeSc.lean`, `Fk/FvSmall.lean`, `Fk/LuMarshal.lean`, `Fk/LuReject.lean`). 리뷰 측정: Scalars accept 생성 전술 146줄 중 130줄이 손 증명에 글자 그대로 있다. 그래서 이것은 "손 증명을 Desc·지시 목록에 맞춰 틀로 재구성한다"이다. 새 명령어나 새 갈래에는 새 손 조각이 필요하다.
- 문장은 Desc와 배치에서 만들지만, 꼴은 손 정리의 문장을 본뜬 것이다(SAME 비교가 그것을 확인한다).

## 3. Scalars 조각 (첫 조각)

`results/attempts-scalars.json`, `compare-scalars.json`, `negative-scalars.json`, `axioms-scalars.json`.

| 의무 | 상태 |
| --- | --- |
| size | 생성 증명 통과, 문장 SAME(`sc_size_main`) |
| accept | 생성 증명 통과(시도 2), 문장 SAME(`sc_accept_main`) |
| reject r2 bool | 생성 증명 통과(시도 2), 문장 SAME(`sc_reject_bool_main`) |
| reject r1 size | 설계 1은 3회 실패(`ecancel`; 시도 2·3은 시도 1에 한 줄을 더하거나 `try`로 감싼 땜질이었다. 접근은 같았다). 설계 2(`Fk/ScReject.lean`의 `h_mem'` 재배열과 `sym`/`kstep` 틀)로 생성 증명 통과, 문장 SAME(`sc_reject_size_main`) |
| marshal | 생성 증명 통과(시도 1), 문장 SAME(`sc_marshal_main`) |
| 조합 | 생성 증명 통과(시도 1, 생성한 accept·marshal 위), 문장 SAME(`sc_unmarshal_then_marshal`). 전 전제 증인 `Gen1cX4.WitScComp`(gen/wit 출력을 생성 정리로 다시 겨눔) |

## 4. ListU64 조각 (손 주 정리가 있는 고정 목록 행 9개 모두 생성; growslice 호출 지점과 r1 프레임 변형은 제외)

리스트 타입에서 Desc가 문장에 주는 값은 `size_stmt`의 원소 크기 하나뿐이다(리뷰 r6 S3). 나머지 Desc 값(원소 크기 8, 한도 16, 고정부 4)은 틀을 고르는 문지기다. 그 밖의 값(프레임, 오프셋, 레이블)은 코드와 Go 배치에서 온다. 생성 모듈 머리 주석도 그렇게 적는다.
`results/attempts-listu64.json`, `compare-listu64.json`, `negative-listu64.json`, `axioms-listu64.json`.
틀은 `Fk/LuMarshal.lean`(size), `Fk/LuReject.lean`(짧은 길이, 첫 오프셋), `Fk/LuRejectCall.lean`(fmt.errorf 경로 둘)의 조각을 따른다.
보조정리 `Gen1cX4.off4`와 fmt.errorf 경로의 일반 보조정리 8개(`staticBox_congr`, `and7_ne`, `and7_zero'`, `shr3_toNat'`, `jg16_true`, `store_avx_step`, `lr_split16`, `join4`)는 `Support.lean`에서 같은 문장으로 다시 증명했다(손으로 씀).
fmt.errorf 경로의 산술 보조정리(`ar_*`)는 생성한다: 프레임 크기, 인자 배열 오프셋, 호출 슬롯에서 숫자를 정하고 `bv_omega`로 증명한다.
경로 값(실패 검사의 점프 대상, 인자 배열 오프셋, 두 호출 지점, 오류 전역, 형식 문자열, `int` 타입 단어)은 지시 목록에서 읽는다.
형식 문자열과 타입 단어는 include 어댑터로 API 항목(`luFmtMis`, `luFmtTooBig`, `intType`)에 묶는다. 항목이 없으면 생성기가 거부한다.
계약 적용 블록(`ConvT64C`, `FmtErrorfDWC`)은 손 증명 글에 값을 넣은 것이다.
측정: 생성 전술 줄 중 손 증명에 글자 그대로 있는 줄은 정렬 191/217, 한도 초과 193/221, accept 205/207, `loop_iter` 80/80, marshal과 `mloop_iter`는 `verbatim_measure`에 있다(`attempts-listu64.json`의 `verbatim_measure`).
accept와 루프는 손 증명과 거의 같은 글이다. 생성기가 하는 일은 지시 번호, 프레임 오프셋, 호출 지점, 타입 단어를 코드에서 읽고 맞지 않는 모양을 거부하는 것이다.
증인 `WitLuAcc`는 `gen/x4/witness.py --runs`가 `Fk/Witness.lean`의 `lu_accept_runs`를 생성 정리로 다시 겨눈 것이다. 그 손 모듈은 구체 Host, 메모리, 계약 인스턴스를 위해서만 가져온다. 이 틀은 8바이트 원소와 한도 16만 받는다. 다른 값은 분류된 거부다.

| 의무 | 상태 |
| --- | --- |
| size | 생성 증명 통과(시도 1), 문장 SAME(`lu_size_main`) |
| reject r1 짧은 길이 | 생성 증명 통과(시도 1), 문장 SAME(`lu_reject_short_main`) |
| reject r2 첫 오프셋 | 생성 증명 통과(시도 1), 문장 SAME(`lu_reject_offset_main`) |
| reject r3 정렬 | 생성 증명 통과(시도 1), 문장 SAME(`lu_reject_misaligned_main`). 변이 `lu-mis-test` |
| reject r4 한도 초과 | 생성 증명 통과(시도 1), 문장 SAME(`lu_reject_toobig_main`). 변이 `lu-big-cmp` |
| accept(0·1·16) | 생성 증명 통과(시도 1), 문장 SAME(`lu_accept_main`). 루프 보조정리 `loop_iter`, `loop_exit`, `loop`를 모듈 안에 생성한다(`Fk/LuLoop.lean`의 틀). 증인 `Gen1cX4.WitLuAcc`(n = 0, 1, 16). 변이 `lu-acc-store` |
| marshal(빠른 경로) | 생성 증명 통과(시도 1), 문장 SAME(`lu_marshal_main`). 루프 보조정리 `mloop_iter`, `mloop_exit`, `mloop`를 생성한다. 증인 `Gen1cX4.WitLuM0/M1/M16`(gen/wit 출력을 다시 겨눔). 변이 `lu-marshal-off` |
| marshal reject r1 한도 초과 | 생성 증명 통과(시도 1), 문장 SAME(`lu_marshal_reject_main`). marshal 틀의 두 번째 모드. 변이 `lu-mrej-cmp` |
| growslice 호출 지점(`lum_grow_site`), r1의 프레임 보존 변형(`lu_reject_short_frame`) | 시도하지 않음(고정 목록의 주 정리 행이 아니거나 같은 행의 보강) |
| 조합 | 생성 증명 통과(시도 1, 생성한 accept·marshal 위), 문장 SAME(`lu_unmarshal_then_marshal`). 증인 `Gen1cX4.WitLuComp`(gen/wit 출력을 다시 겨눔, n = 1). 변이 `lu-compose-len`(문장) |

## 5. ListC 조각 (손 주 정리가 있는 고정 목록 행 10개 모두)

`results/attempts-listc.json`, `compare-listc.json`, `negative-listc.json`, `axioms-listc.json`.
ListU64의 거부 틀을 넓혔다: 스택 가드 거리 G(`lea -G(%rsp),%r12`)와 `sub $F,%rsp` 꼴 프레임을 코드에서 읽는다.
G = 8이면 ListU64 문장(`hsp` 전제), 아니면 `guard + G < rsp` 전제와 생성 보조정리 `ar_neg{G}`를 쓴다(손 문장 `lc_reject_*_main`의 꼴).
ListU64 출력은 이 변경 뒤에도 바이트가 같다.
원소가 컨테이너인 리스트는 원소를 건드리지 않는 틀(r1, r2)만 받는다. 다른 의무는 분류된 거부다.

| 의무 | 상태 |
| --- | --- |
| reject r1 짧은 길이 | 생성 증명 통과(시도 1), 문장 SAME(`lc_reject_short_main`). 변이 `lc-short-cmp` |
| reject r2 첫 오프셋 | 생성 증명 통과(시도 1), 문장 SAME(`lc_reject_offset_main`). 변이 `lc-off-jne` |
| size | 생성 증명 통과(시도 1; logs/97 비교 단계는 대조군 import 누락으로 오류, logs/98에서 비교만 다시), 문장 SAME(`lc_size_main`). 바깥 항목 루프 보조정리 `size_iter`, `size_loop`를 생성한다(`Fk/LcSize.lean`의 틀). 변이 `lc-size-init`. 손 글 비율: `size` 21/23, `size_iter` 30/30, `size_loop` 36/37줄이 `Fk/LcSize.lean`에 글자 그대로 있다(`gen/x4/verbatim.py`). 생성기가 코드에서 정하는 것: 두 레이블 위치, 바깥 Go 오프셋, 포인터 보폭 8, 안쪽 길이 오프셋, 안쪽 원소 너비(`lea` 배율), 항목당 상수 8. 각각을 Desc(오프셋 4 + 안쪽 고정부 4 + w·len)와 layout.json에 맞춘다. `lcAcc`(`Support.lean`, 손으로 씀)가 8 + 8·l로 고정이라 안쪽 너비 8만 받는다 |
| reject r3 첫 오프셋 0, r6 끝을 넘는 오프셋, r10 5..7바이트 | 생성 증명 통과(시도 1, logs/99), 문장 SAME(`lc_reject_zero_main`, `lc_reject_past_main`, `lc_reject_tail_main`). 변이 `lc-zero-je`, `lc-past-ja`, `lc-tail-add`. `fmt.errorf`(인자 없음, 계약 `FmtErrorfNilC`) + `runtime.newobject`(계약 `NewobjectC`) 경로의 지시 종류별 걷기. 생성기가 코드에서 정하는 것: 경로(어느 조건 점프를 타는지), 지시 번호, 프레임 0xd8과 호출 슬롯, 두 호출 지점, 형식 문자열(include API 항목 `lcFmtZero`, `lcFmtShort`에 묶음), newobject 타입 단어, 항목 한도(`cmp $0x4,%rdx` = Desc 한도 4). 갈래를 닫는 조각과 계약 블록, 모드별 경로 전제는 손 글이다. 손 글 비율: r3 152/162, r6 179/189, r10 148/158줄이 `Fk/LcReject.lean`에 글자 그대로 있다. 나머지 줄은 보조정리·데이터 이름(`ar_*`, `fmt_*`, `Fk.Data.*`)과 `intro` 줄만 다르다(diff로 확인). 일반 보조정리 9개(`lc_rdx4`, `jle3_*`, `zx_o`, `and3_*`, `shr2_o`, `ja4_false`, `jae_false`)는 `Support.lean`에 같은 글로 다시 씀(손) |
| accept(바깥 0·1·4 × 안 0·1·16) | 생성 증명 통과(시도 1, logs/100), 문장 SAME(`lc_accept_main`, `lc_accept_empty_main`; logs/101). `gen/x4/lcacc.py`가 항목 루프 `lcl_iter`/`lcl_exit`/`lcl_loop`와 두 수용 경로를 만든다. 생성기가 코드에서 정하는 것: 레이블 위치(루프 머리·출구, 마지막 항목 갈래, 합류, 루프 본문, 반환 블록, 수용·빈 목록 갈래), 호출 지점 셋(makeslice, newobject, 원소 디코더; 원소 타입은 layout.json과 맞춤), 타입 단어 둘, 조건 점프마다 탐/안 탐(오류 블록 규칙: 모든 길이 fmt.errorf·panicBounds·ssz.Err*에 닿는 블록으로 가는 점프는 안 탄다, 넘어가는 쪽이 그런 블록이면 탄다, writeBarrier = 0, 루프 머리 `jae`와 마지막 항목 `je`는 경우 나눔), 지시 번호, 스필·재적재마다 프레임 칸과 그 값(레지스터·칸 표). 앞부분 0..42는 fmt.errorf(nil) 걷기를 수용 모드로 다시 쓴다. 손 글: 모든 문장(`lcacc_tpl.py`, 손 모듈에서 코드 이름·레이블·호출 지점·타입 단어만 자리표시로 바꿔 복사), `lcl_loop` 증명 전체, 호출·계약 블록, 항목 배열 저장, 오프셋 표 적재, 갈래 닫기·마무리 조각. 프레임 배치는 생성하지 않는다: 프레임 0xd8, 가드 0x60, 스필 칸 집합이 다르면 거부한다. 손 글 비율: `lcl_iter` 500/500(손 증명과 글자까지 같다), `lcl_exit` 11/11, `lcl_loop` 59/59, accept 294/298, accept_empty 114/118. 문장 정의 `lcObjs`·`ptrBytes`·`lcStart`·`lcStk`와 보조정리는 `lean/Gen1cX4/SupportLc.lean`(손, 같은 글). `lcObjs`가 구조 재귀라서 똑똑한 펼침이 켜져 있으면 `isDefEq`가 변수 인자에서 두 사본을 못 펼친다(logs/100 비교: accept DIFF). 비교를 똑똑한 펼침 없이 하면 SAME(`pairs-listc.json`의 `no_smart_unfolding`). 다른 ListC 쌍과 대조군은 결과가 같다. 증인 `Gen1cX4.WitLcA1`, `WitLcA1x1`, `WitLcA4`, `WitLcA4x16`, `WitLcAMix`, `WitLcE`(gen/wit 출력을 다시 겨눔, logs/103). 변이 `lc-acc-cap`(accept), `lc-loop-next`(`lcl_iter` 안), `lc-empty-avx`(accept_empty) |
| reject r8 오프셋 순서 | 생성 증명 통과(시도 1; logs/105는 증인 병렬 재빌드가 메모리 캡에 멈춤, logs/106에서 모듈마다 따로 빌드해 통과), 문장 SAME(`lc_reject_offset_order_main`). `lcacc.py` 항목 루프 걷기의 order 모드: 마지막 항목 `je`의 아닌 갈래, 순서 검사 `jb`(`cmp %r11,%rsi`)를 거부 블록으로 탄다. 블록 모양(convT64 둘, fmt.errorf, jne, retq)을 검사하고 형식 문자열·타입 단어를 API 항목 `lcFmtOrder`, `uint64Type`에 묶는다. 거부 블록 글 전체와 문장은 손 글(`Fk/LcOrder.lean`). 손 글 비율 `lcl_order` 262/266, 주 정리 258/262. 증인 `Gen1cX4.WitLcO`(손 보조정리 `lcFmtOrder_len`을 같은 문장의 생성 `fmt_len_lcFmtOrder`로 바꿈, `witness.py --rename`). 변이 `lc-order-jb`(`lcl_order` 안) |
| reject r9 원소 오류 | 생성 증명 통과(시도 1, logs/109), 문장 SAME(`lc_reject_item_main`). `lcacc.py` item 모드: 마지막 항목 갈래, 원소 디코더 호출(계약 `LuURejShortC`), 그 뒤 `jne`를 `Items: %w` 거부 블록으로 탄다. 블록 모양을 검사하고 형식 문자열을 API 항목 `lcFmtItems`에 묶는다. 주 정리의 `intro` 줄은 문장의 묶음 이름에서 만든다. 문장, 호출 블록, 거부 블록은 손 글(`Fk/LcItems.lean`). 계약 문장 `LuURejShortC`는 `SupportLc.lean`에 같은 글로(명시 `[Host]`) 다시 씀. 손 글 비율 `lcl_itemerr` 256/259, 주 정리 259/263. 증인 `Gen1cX4.WitLcI`(계약 인스턴스 보조정리 `lu_urej_short_holds`만을 위해 손 모듈 `Fk.LcItems`를 가져온다, `witness.py --extra-import`; logs/110). 변이 `lc-item-jne`(`lcl_itemerr` 안) |
| marshal(빠른 경로, 루프 넷) | 생성 증명 통과(logs/113; 부정 시험은 생성기 import 결함으로 logs/113에서 4건 모두 기대 밖, 고친 뒤 logs/114에서 4/4), 문장 SAME(`lc_marshal_main`). **다른 ListC 행보다 약하다**: 지시 종류별 걷기가 없다. `lcmarsh.py`는 `MarshalSSZTo.S`의 레이블 위치만 읽고, 손 글의 지시 번호 113개를 (레이블, 오프셋)으로 다시 놓는다. 그 지시마다 손 사례의 명령어 글과 같아야 하고 다르면 거부한다. 문장, 루프 넷(`lcm1..4`), 정의, 전술 글 전체가 손 글(`lcm_tpl.py`, `Fk/LcMarshal.lean`). 손 글 비율 marshal 183/184, 루프 보조정리 100%. 보조 항목(`offTab` 등)은 `SupportLc.lean`에 같은 글. 증인 `WitLcM0/M1/M1x1/M4/M4x16/MMix`(logs/116). 변이 `lc-marshal-len`(marshal 안), `lc-mloop-off`(`lcm2_iter` 안) |

## 6. 축약 Checkpoint·AttestationData (`target/prysm`, Go 1.26.3 ELF의 손 타입)

`results/attempts-{checkpoint,attestationdata}.json`, `compare-*`, `negative-*`, `axioms-*` 같은 이름.
**가장 약한 생성 방식이다.** `anchor.py`는 지시 종류별 걷기를 하지 않고, 손 틀 파일도 따로 두지 않는다.
- 틀: 손 정리와, 그 정리가 이름으로 쓰는 같은 타입 손 모듈의 선언(닫힘)을 생성할 때 그대로 복사한다(`Fk/CpAccept.lean`, `Fk/CpMarshal.lean`, `Fk/CpSpec.lean`). 그 손 모듈은 import하지 않는다.
- 코드가 정하는 것: 대상 함수의 레이블 위치와, 그로부터 글 안의 모든 지시 번호(`kat`, `klabel`, `k + N`: 손 코드에서 레이블 j + 오프셋 o → 대상에서 레이블 j + o), rip 기호 피연산자(`type__+N` 등, 위치로 짝지음).
- 검사: 대상 함수 전체를 정규화(자기 레이블 → 순번, 기호 → 첫 사용 순번)해서 손 함수와 같아야 한다. 다르면 처음 다른 지시와 함께 거부한다. 그래서 이 틀은 손 사례와 레이블 배치·기호 주소만 다른 코드에만 맞는다.
- Desc 문지기(`anchor.desc_gate`): SizeSSZ = `mov $고정크기,%eax`, 디코더 `cmp $고정크기,%rcx`, 바이트 벡터마다 그 길이의 makeslice 하나, 컨테이너 필드마다 newobject 하나, 인코더의 바이트 벡터마다 memmove 하나.
- 손 글 비율: size 9/10, accept 182/183, reject_size 62/63, marshal 138/139, marshal_reject 90/91줄. 나머지 한 줄은 생성한 `intro` 줄이다.

| 의무 | 상태 |
| --- | --- |
| size, accept, reject r1 크기, marshal, marshal_reject r1 | 생성(고정 틀) 증명 통과(시도 1, logs/117), 문장 SAME(`cp_size_main`, `cp_accept_main`, `cp_reject_size_main`, `cp_marshal_main`, `cp_marshal_reject_main`), 대조군 DIFF 4, 공리 표준만(10개 이름), 변이 5개가 지정 정리 안에서 실패·대조군 5개 통과. 증인 `Gen1cX4.WitCpAcc`, `WitCpM`, `WitCpMR`(손 증인의 runs 정리를 `witness.py --runs`로 다시 겨눔, logs/118) |
| reject_complete | 시도하지 않음: 손 행이 부분이고 EthLib 쪽 정리(`cp_spec_accepts_iff`)뿐이다. 기계어 의무가 아니다 |
| reject_spec r1, 조합 3행 | 시도하지 않음: 손 정리가 없다 |
| AttestationData size, accept, reject r1 크기, marshal | 생성(고정 틀) 증명 통과(시도 1, logs/119), 문장 SAME(`ad_size_main`, `ad_accept_main`, `ad_reject_size_main`, `ad_marshal_main`), 대조군 DIFF 4, 공리 표준만(23개 이름), 변이 4개 지정 정리 안에서 실패·대조군 4개 통과. 증인 `WitAdAcc`, `WitAdM`. 손 글 비율 9/10, 556/557, 62/63, 437/438. 손 보조 선언 19개를 복사했다(Cp·Ad 손 모듈은 import하지 않음). 다른 타입의 손 모듈(`Fk.NeAccept`, `Fk.LcReject`, `Fk.FvAccept` 등)은 일반 보조정리 때문에 import한다 |
| AttestationData reject r2/r3, unreachable_mc r2/r3, marshal_reject r1..r3, reject_spec, 조합 | 시도하지 않음: 손 정리가 없다 |
