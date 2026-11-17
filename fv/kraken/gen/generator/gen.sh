#!/bin/sh
# Run gen/generator/generator.py on every row of gen/generator/types.tsv (its header comment gives the columns).
# Usage: sh fv/kraken/gen/generator/gen.sh [<out dir>]   (from any directory)
# Without <out dir>: an accept row writes lean/Prysm/<type>/GeneratedDecodeAccept.lean (modes uint64 and
# decoder --whole-accept) or lean/Prysm/<type>/GeneratedEncodeFastPath.lean (mode encoder --fast-path).
# With <out dir>: nothing goes into the tree. Each row writes <out dir>/<type>.<part>.rc and .stderr.
# An accept row also writes <out dir>/<type>.<part>.lean. <part> is uint64, whole-accept or fast-path.
# The modes decoder --whole-accept and encoder --fast-path also write <out dir>/<type>.<part>.summary.json.
# The last line of the .stderr file of a refuse row gives the reason of the refusal.
# An accept row must exit 0 with an output. A refuse row must exit 2 with nothing on standard output.
# For a row with another result, the script names the row, writes no output file and exits 1 at the end.
# Check the outputs with gen/checks/regenerate_and_compare.py.
# Each output has the namespace Prysm.<type>.
# The code constant (--const) is the short name in the code namespace Prysm.<type>.Code that --open opens.
# The prefix of the generated names (--name, --prefix) names the mode:
#   Decode.generated_accept (uint64), Decode.generated (decoder --whole-accept), Encode.generated (encoder --fast-path).
set -u
if [ $# -gt 1 ]; then
  sed -n '2,11p' "$0" >&2
  exit 2
fi
OUT=
if [ $# -eq 1 ]; then
  mkdir -p "$1" && OUT=$(cd "$1" && pwd) || exit 2
fi
cd "$(dirname "$0")/../.." || exit 2
TABLE=gen/generator/types.tsv
N=prysm/go1.26.10/link-set/norm
TAB=$(printf '\t')
TMP=$(mktemp -d) || exit 2
trap 'rm -f "$TMP/out" "$TMP/err"; rmdir "$TMP"' EXIT
errors=0
error() {
  echo "gen.sh: $TABLE line $n: $pkg $t $mode: $1" >&2
  if [ -s "$TMP/err" ]; then tail -n 3 "$TMP/err" >&2; fi
  errors=$((errors + 1))
}
n=0
while IFS=$TAB read -r pkg t mode opts expect companions; do
  n=$((n + 1))
  : > "$TMP/err"
  case $pkg in
    '#'* | '' | package) continue ;;
    v1alpha1) P=github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1 ;;
    v1) P=github.com_OffchainLabs_prysm_v7_proto_engine_v1 ;;
    primitives) P=github.com_OffchainLabs_prysm_v7_consensus_types_primitives ;;
    *) error "unknown package"; continue ;;
  esac
  if [ -z "$companions" ]; then
    error "a row has six columns, separated by one tab"
    continue
  fi
  case $mode in
    uint64)
      part=uint64; file=GeneratedDecodeAccept
      set -- uint64 --assembly $N/$P.$t.UnmarshalSSZ.S --const unmarshalSSZ --name Decode.generated_accept \
        --imports Codec.Uint64Decoder,Prysm.$t.Code --open Prysm.$t.Code ;;
    'decoder --whole-accept')
      part=whole-accept; file=GeneratedDecodeAccept
      set -- decoder --whole-accept --assembly $N/$P.$t.UnmarshalSSZ.S --const unmarshalSSZ --ir prysm/ir/ir-mainnet.json \
        --type $pkg.$t --prefix Decode.generated --imports Prysm.$t.Code --open Prysm.$t.Code ;;
    'encoder --fast-path')
      part=fast-path; file=GeneratedEncodeFastPath
      set -- encoder --fast-path --assembly $N/$P.$t.MarshalSSZTo.S --const marshalSSZTo --ir prysm/ir/ir-mainnet.json \
        --type $pkg.$t --prefix Encode.generated --imports Prysm.$t.Code --open Prysm.$t.Code ;;
    *) error "unknown mode"; continue ;;
  esac
  if [ "$opts" != - ]; then
    # shellcheck disable=SC2086
    set -- "$@" $opts
  fi
  if [ -n "$OUT" ] && [ $part != uint64 ]; then
    set -- "$@" --summary "$OUT/$t.$part.summary.json"
  fi
  python3 -I -B gen/generator/generator.py "$@" < /dev/null > "$TMP/out" 2> "$TMP/err"
  rc=$?
  if [ -n "$OUT" ]; then
    echo $rc > "$OUT/$t.$part.rc"
    cat "$TMP/err" > "$OUT/$t.$part.stderr"
  fi
  case $expect in
    accept)
      if [ $rc -ne 0 ] || [ ! -s "$TMP/out" ]; then
        error "expected accept (exit 0 and an output), the generator exits $rc"
      elif [ -n "$OUT" ]; then
        cat "$TMP/out" > "$OUT/$t.$part.lean"
      else
        cat "$TMP/out" > lean/Prysm/$t/$file.lean
      fi ;;
    refuse)
      if [ $rc -ne 2 ] || [ -s "$TMP/out" ]; then
        error "expected refuse (exit 2 and nothing on standard output), the generator exits $rc with $(wc -c < "$TMP/out") bytes"
      fi ;;
    *) error "expect is not accept or refuse" ;;
  esac
done < "$TABLE"
if [ $errors -ne 0 ]; then
  echo "gen.sh: $errors rows with a result that the table does not expect" >&2
  exit 1
fi
