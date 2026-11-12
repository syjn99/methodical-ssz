# Proposed shared-document changes (phase 1c, apply after the rebase)

INBOX 003 item 2: the principle is approved. Apply it after the fix3 rebase. Do not change the shared documents now.
The sentences below are drafts. At that time, put them in `DIRECTION.md` section 5 and `TOOLS.md` "Fixed versions".

## DIRECTION.md section 5 (change only the 1c part)

> The 1c Prysm source is `ab15ff70c72a568c870b2de662474685a95de294` (slice + `ssz-size`). We do not claim that it is the same as the fixed-array pin.
> The 1c target compiler is Go 1.26.10. It is a new experimental baseline with a separate namespace (`prysm/go1.26.10/MANIFEST.md`).
> The theorems of the Go 1.26.3 ELF `9c850c97…c501` do not carry over to this machine code.
> Superseded history: 1c pin `5ac1d028f5` (pin branch `45394e5`), 1c compiler Go 1.26.3. The values of fix 3 do not change.

## TOOLS.md fixed-version table (add rows)

| Item | Value | Where it is fixed |
| --- | --- | --- |
| 1c Prysm source | `ab15ff70c72a568c870b2de662474685a95de294`, generation only in a temporary tree | `prysm/go1.26.10/MANIFEST.md` |
| 1c Go | 1.26.10, cross-compile to linux/amd64 on host linux/arm64, `GOAMD64=v1 CGO_ENABLED=0 -tags purego -trimpath` | `prysm/go1.26.10/build-ids.txt` |
| 1c ELF | sha256 `c6403c02…911e` (not committed, rebuild command in MANIFEST) | `prysm/go1.26.10/build-ids.txt` |
