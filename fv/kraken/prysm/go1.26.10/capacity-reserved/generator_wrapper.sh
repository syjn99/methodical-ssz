#!/bin/sh
# Generator wrapper for the capacity-reserving generator option: adds --reserve-marshal=Checkpoint to the phase0.yaml runs only.
# Usage (as GEN of fv/kraken/gen/prysm-gen.sh): CAPACITY_RESERVED_GEN=<ssz binary> generator_wrapper.sh <args...>
for a in "$@"; do
  if [ "$a" = "--config=proto/prysm/v1alpha1/phase0.yaml" ]; then
    exec "$CAPACITY_RESERVED_GEN" "$@" --reserve-marshal=Checkpoint
  fi
done
exec "$CAPACITY_RESERVED_GEN" "$@"
