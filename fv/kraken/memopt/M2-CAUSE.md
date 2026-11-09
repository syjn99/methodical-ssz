# M2: WitLcM4x16 메모리 원인 분리

판정: 주원인은 `u64v0`–`u64v3`의 `by decide`가 elaboration 단계에서 `u64Bytes`를 계산하는 비용이다.
근거는 A2(13.24 GiB), C6(kernel 생략, 4.29 GiB), C10(같은 명제를 `simp`로 증명, 전체 파일 1.42 GiB)이다.

- 모델: Claude Opus 5.5 (`claude-opus-5-5`, 시스템 프롬프트 기준).
- Orca 터미널: `ORCA_TERMINAL_HANDLE=term_5525b821-81d4-44d5-8522-8a65fedc6917`.
- Claude Code 세션 ID: `86e99ddd-2f6f-44bb-ab17-3e2f399311d8` (scratchpad 경로에서 읽었다).
- 기준: 브랜치 `syjn99/ssz-fv-memopt`, HEAD `daa9dbc`. 환경은 `ENV.md`와 같다.
- 공개 파일(`Fk/*.lean`, 생성기, helper, `Fv1`, `Fv`)은 바꾸지 않았다.

## 1. 방법

- 진단 파일은 `scratch/*.lean`이다. `scratch/gen.py`가 `86fd060`의 `Fk/WitLcM4x16.lean`의 줄을 잘라 만든다.
- `A4.lean`은 원본과 바이트 단위로 같다(`diff` 출력 없음).
- 모든 측정은 `fv/kraken/lean`에서 `../memopt/measure.sh <label> lake env lean ../memopt/scratch/<f>.lean`이다.
- B2, B3만 원본 `Fk/WitLcM4x16.lean`을 측정했다. 명령은 표에 적는다.
- peak RSS는 `/usr/bin/time -l`의 최대 단일 프로세스 값이다. 로그는 `logs/<label>.*`이다.
- 측정 중 다른 Lean 프로세스는 없었다(`pgrep` 확인).
- 진단 파일에 `sorry`, `axiom`, `native_decide`는 없다.
- C6, C7은 `set_option debug.skipKernelTC true`를 쓴다. 이 두 파일은 kernel 검사를 생략한다. 증명으로 쓰지 않는다.
- "머리"는 원본 1–43줄이다(import, `host`, `objs`, `u64nil`까지). A0는 머리만 있다.

## 2. 측정 표

| 진단 파일 | 가설 | exit | peak RSS (GiB) | wall (s) |
| --- | --- | --- | --- | --- |
| A0 | 머리만: 기준선 | 0 | 1.35 | 2.78 |
| A1 | 머리 + `u64v0` | 0, 0 | 4.30, 4.30 | 9.00, 8.37 |
| A2 | 머리 + `u64v0`–`u64v3` | 0, 0 | 13.24, 13.23 | 15.28, 15.41 |
| A3 | A2 + `block`, `mem`, `s0` | 0, 0 | 13.25, 13.25 | 15.42, 15.51 |
| A4 | 원본 전체 (대조군) | 0, 0 | 13.28, 13.30 | 15.56, 15.63 |
| B1 | A4 + `set_option Elab.async false` | 0, 0 | 5.37, 5.37 | 27.86, 27.68 |
| B2 | 원본, `LEAN_NUM_THREADS=1 lake env lean Fk/WitLcM4x16.lean` | 0, 0 | 13.26, 13.27 | 15.61, 15.81 |
| B3 | 원본, `lake env lean -j1 Fk/WitLcM4x16.lean` | 0, 0 | 4.31, 4.31 | 27.82, 27.65 |
| C0 | 머리 + `u64v0 := by decide` (A1과 같다) | 0 | 4.30 | 8.54 |
| C1 | `u64v0 := by decide +kernel` | 0, 0 | 2.38, 2.38 | 5.09, 5.15 |
| C2 | `u64v0 := by rfl` | 0 | 4.37 | 8.12 |
| C3 | `u64v0 := by simp [u64Bytes, uintBytes]` | 0, 0 | 1.35, 1.35 | 2.83, 2.78 |
| C4 | List 보조정리 + `rw; decide` | 0, 0 | 1.38, 1.39 | 2.94, 2.89 |
| C5 | List 보조정리 + `simp only` + `decide` | 0 | 1.35 | 2.79 |
| C6 | C0 + kernel 생략 (elaboration만) | 0, 0 | 4.29, 4.29 | 6.62, 6.75 |
| C7 | A2 + kernel 생략 (elaboration만) | 0 | 13.23 | 7.17 |
| C8 | 원본 전체, 네 `u64v`를 C4 방법으로 | 0, 0 | 1.50, 1.48 | 3.57, 3.64 |
| C9 | 원본 전체, `u64v1`–`u64v3 := u64v0` | 0, 0 | 4.36, 4.33 | 8.45, 8.52 |
| C10 | 원본 전체, 네 `u64v`를 C3 방법으로 | 0, 0 | 1.42, 1.42 | 5.51, 3.90 |
| D1 | A4, `objs`·`block`·`mem`·`s0`에 `noncomputable` | 0 | 13.26 | 15.44 |
| E1 | `u64Bytes` decide, 원소 1개 | 0 | 1.35 | 2.77 |
| E4 | 원소 4개 | 0 | 1.35 | 2.90 |
| E8 | 원소 8개 | 0 | 1.52 | 3.25 |
| E12 | 원소 12개 | 0 | 2.27 | 4.80 |
| E16 | 원소 16개 (명제는 `u64v0`와 같다) | 0 | 4.30 | 8.27 |

C4, C5의 List 보조정리는 다음 두 개다. 둘 다 일반 정리이고 귀납 또는 `simp`로 증명했다.

```lean
theorem m2_uintBytes_succ (w v : Nat) :
    (uintBytes (w + 1) v).toList = UInt8.ofNat (v % 256) :: (uintBytes w (v / 256)).toList
theorem m2_u64Bytes_toList (l : List UInt64) :
    (u64Bytes l).toList = l.flatMap (fun x => (uintBytes 8 x.toNat).toList)
```

A4의 peak는 M1 값(13.01–13.27 GiB)과 같은 범위다. A4의 wall은 M1(17.71–18.48 s)보다 짧다. 그 차이의 원인은 측정하지 않았다.

## 3. 결론

### 3.1 급증 지점 (선언)

- `u64v` decide 하나는 기준선보다 2.95 GiB를 더 쓴다(A1 4.30 − A0 1.35).
- 네 개는 11.89 GiB를 더 쓴다(A2 − A0). 이것은 하나의 4.03배다.
- `block`, `mem`, `s0`의 몫은 0.01–0.02 GiB다(A3 − A2).
- `s_mem`, `lc_marshal_runs`의 몫은 0.03–0.05 GiB다(A4 − A3).
- `u64v`가 싼 전체 파일(C8, C10)은 1.42–1.50 GiB다. 그래서 나머지 선언은 기준선보다 0.15 GiB 이하를 더 쓴다.

### 3.2 단계 (elaboration, kernel, 컴파일)

- elaboration이 peak를 정한다. kernel을 생략해도 peak가 같다(C6 4.29 대 C0 4.30, C7 13.23 대 A2 13.24).
- kernel만 쓰면 peak가 작다(C1 `decide +kernel` 2.38 GiB). kernel 몫은 기준선보다 1.03 GiB다.
- `by rfl`도 같은 크기다(C2 4.37 GiB). 정의 전개로 같음을 보이는 방법은 모두 비싸다.
- 컴파일은 원인이 아니다. `noncomputable`은 peak를 바꾸지 않았다(D1 13.26 대 A4 13.28–13.30).

### 3.3 가설 판정: "kernel/whnf의 `Array.append` 축약이 주원인이다"

- 계산 부분은 측정과 맞다. `Array ++` 사슬을 List로 바꾸면 비용이 사라진다(C4 1.38 GiB).
- C4에서도 각 원소의 `uintBytes 8`(크기 8 이하의 `Array ++`)은 `decide`가 계산한다. 그 비용은 작다.
- 그래서 비용은 16단계로 커지는 `Array ++` 사슬에 있다. 이 결론은 제거 실험에 근거한다. whnf 내부는 프로파일하지 않았다.
- 단계 부분은 반박된다. 주 단계는 kernel이 아니고 elaboration(`decide`의 Meta 수준 평가)이다.

### 3.4 크기 스케일

- 기준선보다 더 쓰는 메모리: 원소 8개 0.17, 12개 0.92, 16개 2.95 GiB.
- 증가는 초선형이다. 세 점에 맞추면 원소 수의 약 4제곱이다(8→12: 지수 4.2, 12→16: 지수 4.1).
- 원소 1, 4개의 비용은 기준선(import peak) 아래에 숨는다. 그래서 그 증가량은 0으로 보인다.
- 그래서 원소 수가 작은 증인은 이 비용을 보여 주지 못한다. M1의 `WitLcM1x1`이 1.36 GiB인 것과 맞다.

### 3.5 병렬도와 저메모리 실패

- `Elab.async`가 네 증명을 동시에 elaborate한다. 그래서 peak가 약 4배가 된다(A2/A1).
- `lean -j1`은 peak를 4.31 GiB로 줄인다. wall은 15.6 s에서 27.7 s로 는다(B3).
- `set_option Elab.async false`는 5.37 GiB, 27.8 s다(B1). B3보다 1.06 GiB 크다. 그 원인은 측정하지 않았다.
- `LEAN_NUM_THREADS=1`은 peak를 바꾸지 않았다(B2 13.26–13.27 GiB). 이 머신의 `lean` 단독 실행에서 그렇다.
- `libleanshared.dylib`에는 문자열 `LEAN_NUM_THREADS`가 있다. 어느 경로가 그 값을 읽는지 조사하지 않았다.
- 저메모리 머신의 실패는 이 결과로 설명될 수 있다. 같은 동작이면 peak는 13 GiB 근처로 9.69 GiB를 넘는다.
- 이 설명은 확인되지 않았다. 플랫폼이 다르다(macOS arm64 대 Linux aarch64). `lake build` 아래 측정도 하지 않았다.

## 4. M3 후보 (효과 예상 순)

1. 네 `u64v`의 증명을 `by simp [u64Bytes, uintBytes]`로 바꾼다. 명제는 그대로다.
   - 근거: C10 전체 파일 1.42 GiB, 3.90–5.51 s. 원본 대비 −11.86 GiB.
   - 새 보조정리가 필요 없다. 생성기 `wlcm.py`의 출력 한 줄을 바꾼다.
   - 미확인: `.olean` 의미 비교, 공리 검사, `lake build` 아래 peak, 다른 원소 길이에서 `simp`가 닫히는지.
2. List 보조정리(`m2_u64Bytes_toList`)를 helper에 두고 `rw; decide`로 닫는다.
   - 근거: C8 전체 파일 1.48–1.50 GiB, 3.57–3.64 s.
   - `decide`로 닫으므로 `simp` 정규형에 덜 의존할 수 있다. 이 점은 측정하지 않았다.
   - 보조정리는 `Fv1`이 아닌 witness helper(예: `Fk/WHost.lean`)에 둔다. 위치는 미측정이다.
3. `u64v1`–`u64v3`를 `u64v0`로 증명한다(같은 명제).
   - 근거: C9 전체 파일 4.33–4.36 GiB, 8.45–8.52 s.
   - 단독으로는 1, 2번보다 효과가 작다. 1, 2번과 함께 쓰면 추가 효과는 미측정이다.

빌드 설정(`-j1`, `Elab.async false`)은 후보에서 뺐다. 증명이 아닌 환경을 바꾸고, wall이 1.8배다.

## 5. 미실행 항목

- whnf 또는 kernel 내부의 프로파일(`trace.Meta.whnf` 등)은 실행하지 않았다. 3.3의 결론은 제거 실험에 근거한다.
- `lake build` 아래에서 `LEAN_NUM_THREADS`, `-j`의 효과는 측정하지 않았다.
- 저메모리 Linux 환경의 재현은 하지 않았다.
- A0, C0, C2, C5, C7, D1, E 계열은 1회만 측정했다.
- C8–C10은 scratch 진단이다. 공개 파일 수정, `.olean` 의미 비교, 공리 검사는 M3 범위다.
- 다른 witness(`WitLcA4x16` 등)의 원인 분리는 범위 밖이라서 하지 않았다.

## 6. 재현

`gen.py`는 원본을 git에서 읽는다(`git show 86fd060:fv/kraken/lean/Fk/WitLcM4x16.lean`). 현재 파일은 읽지 않는다.

```sh
cd fv/kraken/lean
python3 ../memopt/scratch/gen.py
for f in A0 A1 A2 A3 A4 B1 C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 D1 E1 E4 E8 E12 E16; do
  ../memopt/measure.sh $f-r1 lake env lean ../memopt/scratch/$f.lean
done
LEAN_NUM_THREADS=1 ../memopt/measure.sh B2-nt1-r1 lake env lean Fk/WitLcM4x16.lean
../memopt/measure.sh B3-j1-r1 lake env lean -j1 Fk/WitLcM4x16.lean
```
