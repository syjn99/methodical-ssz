#!/bin/sh
# Generator wrapper for OPT-R1: adds --reserve-marshal=Checkpoint to the phase0.yaml runs only.
# Usage (as GEN of fv/kraken/gen/prysm-gen.sh): OPTR1_GEN=<ssz binary> gen-wrap.sh <args...>
for a in "$@"; do
  if [ "$a" = "--config=proto/prysm/v1alpha1/phase0.yaml" ]; then
    exec "$OPTR1_GEN" "$@" --reserve-marshal=Checkpoint
  fi
done
exec "$OPTR1_GEN" "$@"
