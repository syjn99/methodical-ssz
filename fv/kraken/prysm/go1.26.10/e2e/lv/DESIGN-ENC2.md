# DESIGN-ENC2: G* (모든 용량의 인코더) 설계

이 파일은 G* 증명 전에 커밋한다. 계획이다.
문장은 `lean/E2eEnc/StmtEncG.lean`에 있다.

## G*

- dst는 `(dp, len, cap)`다. 옛 블록은 `pre ‖ spare`이고 `len + |spare| = cap`이다.
- 덧붙임 자리는 n + 2개다: 자리 1(BlockRoot), 자리 2(WriteOffset), 루프의 n 자리.
- 어느 자리도 growslice를 부를 수 있다. 계약은 `GrowsliceC Heap e2eU8Type_addr 1 S` 하나다.
- 한 번 부를 때 `2·nextSliceCap + 8192` 바이트가 필요하다. 쓰는 양도 그 이하다.
- newLen ≤ L = len + 36 + 8n이고 `nextSliceCap ≤ 2·L + 192`다. 그래서 자리마다 K = 4·L + 8576이면 된다.
- 힙 전제: `(n + 2)·K ≤ avail`. 불변식: 남은 자리가 r개이면 남은 힙 ≥ r·K.

## 사후조건

- 결과 블록: `pre ‖ root ‖ dcOff ‖ cb ‖ rest`, `len + 36 + 8n + |rest| = 결과 cap`.
- 늘릴 때마다 옛 블록(복사된 앞부분과 안 쓴 spare)이 남는다. 그것을 존재 술어 `G`로 묶는다.
- 늘림이 없으면 `G`는 비어 있고 결과 블록은 옛 블록이다.
- 늘림 경로에서만 쓰는 칸(x + 24, x − 16, x − 48, x − 72, spill 40)은 전제에 두고 사후조건에서 존재 변수다.

## 증명 꼴

- 머리(0–28): 자리 1이 맞으면 F의 머리, 아니면 G의 머리. 두 갈래 모두 L_7c(29)에서 같은 꼴의 상태가 된다.
- 꼬리(29–60): memmove, 자리 2(맞음 또는 늘림 45–49), movl, n, Columns 포인터.
- 루프 불변식(82): 블록 = `Pfx ‖ cb.take (8i) ‖ tail`, `|tail| = cp − (L₀ + 8i)`, 쓰레기 `G`, 힙 ≥ (n − i)·K.
  x − 24(pc), x − 40(n)을 불변식에 둔다. 늘림 갈래(90–99)가 그 칸을 다시 읽는다.
- 한 바퀴 정리는 두 갈래다: 맞음(89 `jae` 감) 또는 늘림(94 growslice, 99 `jmp L_132`).
