#!/usr/bin/env python3
"""Write fv/kraken/prysm/TYPES.md from the saved JSON. No number is typed by hand.

Usage: types_md.py <prysm-dir>
Inputs: inventory.json, go1.26.10/functions.json, go1.26.10/kparse.json,
go1.26.10/kparse-riz-diag.json, diff/gendiff.json, go1.26.10/build-ids.txt.
Python 3 standard library only. Run with python3 -I.
"""
import json
import sys
from collections import Counter

ABBR = {"ValidateBitlist": "VBl", "ValidateBitvector": "VBv", "convT64": "cT64", "fmt": "fmt",
        "generated method": "gen", "growslice": "grow", "hand-written primitives method": "hand",
        "makeslice": "mks", "memmove": "mm", "morestack_noctxt": "stk", "newobject": "new",
        "panic*": "pan", "write barrier": "wb", "moveSlice* (stack-backed result to heap)": "mvS",
        "runtime other": "rt?", "other": "oth?", "indirect": "ind"}
METHODS = ("MarshalSSZTo", "SizeSSZ", "UnmarshalSSZ")


def short(pkg):
    return pkg.replace("github.com/OffchainLabs/prysm/v7/", "")


def main():
    d = sys.argv[1]
    inv = json.load(open(f"{d}/inventory.json"))
    fn = json.load(open(f"{d}/go1.26.10/functions.json"))
    kp = json.load(open(f"{d}/go1.26.10/kparse.json"))
    rz = json.load(open(f"{d}/go1.26.10/kparse-riz-diag.json"))
    gd = json.load(open(f"{d}/diff/gendiff.json"))
    bid = dict(l.split(": ", 1) for l in open(f"{d}/go1.26.10/build-ids.txt").read().splitlines() if ": " in l)
    c, fc = inv["counts"], fn["counts"]
    kps = {r["symbol"]: r for r in kp["functions"]}
    rzs = {r["symbol"]: r for r in rz["functions"]}
    funcs = {(f["package"], f["type"], f["method"]): f for f in fn["functions"]}
    L = []
    w = L.append
    w("# TYPES: Prysm Fulu 타입 목록 (phase1c X1)")
    w("")
    w("이 파일은 `fv/kraken/gen/types_md.py`가 저장된 JSON에서 만든다. 손으로 고치지 않는다.")
    w("수치는 모두 프로그램이 센다. 범위 분류는 1차(잠정)다. 증명이 아니다. 게이트 1c 통과가 아니다.")
    w("")
    w("## 1. 요약")
    w("")
    w(f"- 목록 집합 I: 생성 타입 {c['set_I']}개. 설정 타입 A {c['set_A']}개, Fulu 도달 B {c['set_B']}개(생성 {c['set_B_generated']}, 손 작성 {c['set_B_hand_written']}).")
    w(f"- 범위 안 {c['scope_in']}개, 범위 밖 {c['scope_out']}개(잠정). 범위 밖 이유: " +
      ", ".join(f"{k} {v}" for k, v in c["out_primary_reason"].items()) + ".")
    w(f"- B만 보면 범위 안 {c['B_scope_in']}개, 범위 밖 {c['B_scope_out']}개.")
    w(f"- 손 작성 위임 대상(`consensus-types/primitives`) {c['I_hand_written']}개. 이것을 부르는 타입 {c['types_calling_hand_written']}개.")
    w(f"- 생성 함수 {fc['generated_functions_inventory']}개(타입 × 3), 명령어 {fc['generated_instructions']}개, 함수당 최대 {fc['max_instructions']}개.")
    w(f"- 니모닉 수준: 생성 함수 {fc['generated_functions_all_supported']}/{fc['generated_functions_inventory']}개가 Kraken 런타임 파서가 받는 이름만 쓴다.")
    ok_inv = kp["counts"].get("inventory: OK", 0)
    err_inv = kp["counts"].get("inventory: ERR", 0)
    w(f"- 실제 파서 실행: 생성 함수 {ok_inv}개 OK, {err_inv}개 ERR. ERR는 모두 `%riz` 피연산자다(4절).")
    w(f"- `%riz` 때문에 실패한 파일 전부({rz['ok'] + rz['err']}개, I 밖 함수 포함)를 `%riz`만 지운 진단 사본으로 다시 돌렸다. {rz['ok']}개 OK다. 진단일 뿐 변환 결과가 아니다.")
    w(f"- 커밋된 Prysm 파일과의 차이: 변경 블록 {gd['totals']['blocks']}개, 분류 {gd['totals']['classified']}개, 미분류 {gd['totals']['unclassified']}개.")
    w(f"- minimal 프리셋에서 IR이 다른 타입 {c['minimal_differs']}개. 범위 분류가 바뀐 타입 {c['minimal_scope_changes']}개.")
    w("")
    w("## 2. 고정 값")
    w("")
    w("| 항목 | 값 |")
    w("| --- | --- |")
    w("| Prysm 소스 | `ab15ff70c72a568c870b2de662474685a95de294` (slice + `ssz-size`). 옛 핀 `5ac1d028f5`/`45394e5`은 대체됐다 |")
    w("| 생성기·런타임 | `698c2025a73a296b55b95744a8408f3b03b2546b` |")
    w(f"| 대상 컴파일 | `{bid['go']}`(호스트 바이너리)로 linux/amd64 교차 컴파일, `{bid['target']}` |")
    w(f"| 호스트 | {bid['host']} (생성은 arm64 네이티브. x86-64 하드웨어 없음) |")
    w(f"| ELF | sha256 `{bid['elf sha256']}`, {bid['elf size']} 바이트. 커밋하지 않는다(`go1.26.10/MANIFEST.md`) |")
    w(f"| 재현성 | 빈 GOCACHE로 두 번째 빌드: sha256 `{bid['elf b2 sha256']}` |")
    w("| Kraken / EthLib / Lean | `6064eec` / `8621856` / `nightly-2026-09-21` |")
    w("")
    w("Go 1.26.10은 새 실험 기준선이다. Go 1.26.3 ELF `9c850c97…c501`의 정리 55개는 이 기계어에 옮겨지지 않는다.")
    w("")
    w("## 3. 방법")
    w("")
    w("1. `gen/prysm-gen.sh`가 임시 Prysm 트리에서 생성기를 돌린다. 플래그는 Prysm `build/gen/ssz.go`와 같다.")
    w("2. 같은 스크립트가 `gen/invtool`로 생성기 자체의 앞단(`config`, `TypeDefs`, `ParseTypeDef`, 위임 인터페이스 집합)의 IR을 JSON으로 뽑는다.")
    w("3. `gen/inventory.py reduce`가 위임 필드 아래를 잘라 `ir/ir-{mainnet,minimal}.json`을 만든다.")
    w("4. `gen/inventory.py build`가 집합, 종류, 깊이, 범위를 `inventory.json`에 쓴다.")
    w("5. `gen/prysm-elf.sh`가 ELF를 두 번 빌드하고 objdump·nm을 뽑는다. `gen/keepalive.py`가 `main`을 만든다.")
    w("6. `gen/mnemonics.py`가 함수마다 명령어 수, 니모닉, 호출 종류를 센다(`go1.26.10/functions.json`).")
    w("7. `link/conv.py --norm`(읽기만 함)으로 `.S`를 만들고 `gen/kparse/KParse.lean`이 Kraken 런타임 파서를 돌린다(`go1.26.10/kparse.json`).")
    w("")
    for k, v in inv["definitions"].items():
        w(f"- `{k}`: {v}")
    w("")
    w("\"Kraken이 받는가\"의 결정:")
    w("")
    w(f"- 니모닉 수준: 고정 Kraken의 `Kraken/X64/Parser/Basic.lean` `parseInstr` 분기 문자열 {len(fn['kraken_accepted_names'])}개와 `j`/`set`/`cmov` + `parseCondCode?` 조건 코드 {len(fn['kraken_condition_codes'])}개. `conv.py` NORM 형식 {len(fn['conv_norm_forms'])}개는 `nop`으로 센다.")
    w("- 실제 파서 수준: `include_x64_rt`가 쓰는 `Kraken.X64.Parser.parse`를 파일마다 실행했다(로그 사본 `go1.26.10/kparse-log.txt`). 이것이 판정 기준이다.")
    w("- 의미론 수준(`kstep`·정리)은 보지 않았다. 이 표는 분류이고 증명이 아니다.")
    w("")
    w("## 4. 수치")
    w("")
    w("| 항목 | 값 |")
    w("| --- | --- |")
    for k, v in c.items():
        w(f"| `{k}` | {json.dumps(v, ensure_ascii=False)} |")
    for k in ("functions_dumped", "generated_functions_inventory", "generated_functions_not_inventory",
              "hand_written_functions", "missing_generated", "generated_instructions",
              "generated_functions_all_supported", "hand_written_instructions", "all_dumped_unsupported",
              "functions_per_call_kind"):
        w(f"| `{k}` | {json.dumps(fc[k], ensure_ascii=False)} |")
    w(f"| `kparse` | {json.dumps(kp['counts'], ensure_ascii=False)} |")
    w(f"| `kparse_riz_diag` | OK {rz['ok']}, ERR {rz['err']} |")
    w("")
    w("파서 ERR 목록:")
    w("")
    for r in kp["errors"]:
        w(f"- `{short(r['symbol'])}` ({r['group']}): {r['error']}")
    w("")
    w("`%riz`는 GNU objdump가 색인 없는 SIB 바이트를 적는 철자다(`%r12`가 기준 레지스터일 때). 주소는 `(%r12)`와 같다.")
    w("생성기 결함이 아니다. 변환기 또는 Kraken 파서의 빈틈이다(`GENERATOR-FINDINGS.md` 4절).")
    w("")
    w("생성 함수의 니모닉 빈도(I만):")
    w("")
    w(", ".join(f"`{k}` {v}" for k, v in fc["mnemonic_occurrences_inventory"].items()))
    w("")
    w("## 5. 집합의 차이")
    w("")
    w(f"- B 중 생성 타입이지만 A에 없는 것 {c['B_generated_minus_A']}개: " + ", ".join(f"`{short(x)}`" for x in inv["sets"]["B_generated_minus_A"]) + ".")
    w(f"- I 중 A에 없는 것 {c['I_minus_A']}개: " + ", ".join(f"`{short(x)}`" for x in inv["sets"]["I_minus_A"]) + ".")
    w(f"- A 중 B에 없는 것 {c['A_minus_B']}개. 이름은 `inventory.json` `sets.A_minus_B`에 있다.")
    w("")
    w("Fulu가 아닌 설정:")
    w("")
    w("| 설정 | 타입 수 | 이유 |")
    w("| --- | --- | --- |")
    for x in inv["not_fulu"]:
        w(f"| `{x['config']}` | {len(x['types'])} | {x['reason']} |")
    w("")
    w("손 작성 위임 대상(생성기가 만들지 않는 SSZ 메서드):")
    w("")
    w("| 타입 | 부르는 타입 수 |")
    w("| --- | --- |")
    for h in inv["hand_written_delegates"]:
        w(f"| `{short(h['type'])}` | {h['used_by_count']} |")
    w("")
    w("minimal에서 IR이 다른 타입은 `inventory.json` `minimal_differences`에 있다. 범위 분류가 바뀐 것은 위 수치와 같다.")
    w("")
    w("## 6. 타입 표")
    w("")
    w("열: 설정, B(Fulu 도달), 종류, 필드 수, 깊이, 범위(이유), 위임 호출(생성/손), 명령어 수 M/S/U(MarshalSSZTo/SizeSSZ/UnmarshalSSZ), 니모닉 종류 수, Kraken 미지원 니모닉, 파서(M/S/U), 런타임 호출(세 함수 합집합).")
    w("호출 약어: " + ", ".join(f"{v}={k}" for k, v in ABBR.items()) + ".")
    w("")
    w("| 타입 | 설정 | B | 종류 | 필드 | 깊이 | 범위 | 위임 | M/S/U | 니모닉 | 미지원 | 파서 | 호출 |")
    w("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    hand = {tuple(h["type"].rsplit(".", 1)) for h in inv["hand_written_delegates"]}
    for t in sorted(inv["types"], key=lambda t: (t["config"], t["name"])):
        fs = [funcs.get((t["package"], t["name"], m)) for m in METHODS]
        ins = "/".join(str(f["instructions"]) if f else "-" for f in fs)
        mn = set()
        uns = set()
        calls = set()
        kpst = []
        for f in fs:
            if not f:
                kpst.append("-")
                continue
            mn |= set(f["mnemonics"])
            uns |= set(f["unsupported"])
            calls |= set(f["calls"])
            r = kps.get(f["symbol"], {}).get("status", "not run")
            if r == "ERR" and rzs.get(f["symbol"], {}).get("status") == "OK":
                r = "ERR(riz)"
            kpst.append(r)
        ng = sum(1 for cc in t["callees"] if tuple(cc.rsplit("/", 1)) not in hand)
        nh = sum(1 for cc in t["callees"] if tuple(cc.rsplit("/", 1)) in hand)
        scope = t["scope"] + (f" ({', '.join(t['reasons'])})" if t["reasons"] else "")
        w(f"| `{t['name']}` | {t['config'].rsplit('/', 1)[-1].removesuffix('.yaml')} | {'B' if t['in_B'] else ''} | "
          f"{t['kind']} | {t['field_count']} | {t['depth']} | {scope} | {ng}/{nh} | {ins} | {len(mn)} | "
          f"{', '.join(sorted(uns)) or '-'} | {'/'.join(kpst)} | {' '.join(sorted(ABBR.get(x, x) for x in calls))} |")
    w("")
    w("필드 모양 빈도(I 전체): " + ", ".join(f"{k} {v}" for k, v in c["field_shape"].items()) + ".")
    w("")
    open(f"{d}/TYPES.md", "w").write("\n".join(L))
    print(f"TYPES.md: {len(inv['types'])} rows")


if __name__ == "__main__":
    main()
