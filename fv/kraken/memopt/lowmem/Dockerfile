# Image for the memopt low-memory check (M4). Linux aarch64, Lean from elan.
# The toolchain is the exact text of fv/kraken/lean/lean-toolchain.
FROM ubuntu:24.04
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
      curl git python3 ca-certificates build-essential time rsync procps \
    && rm -rf /var/lib/apt/lists/*
ENV ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --no-modify-path --default-toolchain none
ARG TOOLCHAIN=leanprover/lean4:nightly-2026-09-21
RUN elan toolchain install "$TOOLCHAIN" && elan default "$TOOLCHAIN" \
    && git config --global --add safe.directory '*'
