module github.com/OffchainLabs/methodical-ssz/fuzz

go 1.26.10

replace github.com/OffchainLabs/prysm/v7 => ./.prysm

replace github.com/OffchainLabs/methodical-ssz => ./.gen

require (
	github.com/OffchainLabs/prysm/v7 v7.0.0-00010101000000-000000000000
	github.com/golang/snappy v1.0.1-0.20260716114414-9ae09f520e93
)

require (
	github.com/OffchainLabs/go-bitfield v0.0.0-20260504143531-5cbb6d0f5f2e // indirect
	github.com/OffchainLabs/methodical-ssz v0.0.0-20261026091435-c3f77ce44447 // indirect
	github.com/ProjectZKM/Ziren/crates/go-runtime/zkvm_runtime v0.0.0-20251001021608-1fe7b43fc4d6 // indirect
	github.com/beorn7/perks v1.0.1 // indirect
	github.com/bits-and-blooms/bitset v1.22.0 // indirect
	github.com/cespare/xxhash/v2 v2.3.0 // indirect
	github.com/consensys/gnark-crypto v0.18.1 // indirect
	github.com/crate-crypto/go-eth-kzg v1.5.0 // indirect
	github.com/decred/dcrd/dcrec/secp256k1/v4 v4.4.1 // indirect
	github.com/ethereum/c-kzg-4844/v2 v2.1.8 // indirect
	github.com/ethereum/go-ethereum v1.17.4 // indirect
	github.com/holiman/uint256 v1.3.2 // indirect
	github.com/klauspost/cpuid/v2 v2.4.0 // indirect
	github.com/minio/sha256-simd v1.0.1 // indirect
	github.com/munnerz/goautoneg v0.0.0-20191010083416-a7dc8b61c822 // indirect
	github.com/pkg/errors v0.9.1 // indirect
	github.com/prometheus/client_golang v1.24.1 // indirect
	github.com/prometheus/client_model v0.6.2 // indirect
	github.com/prometheus/common v0.70.1 // indirect
	github.com/prometheus/procfs v0.21.1 // indirect
	github.com/prysmaticlabs/gohashtree v0.0.5-beta // indirect
	github.com/sirupsen/logrus v1.9.4 // indirect
	github.com/supranational/blst v0.3.16 // indirect
	github.com/thomaso-mirodin/intmath v0.0.0-20160323211736-5dc6d854e46e // indirect
	golang.org/x/net v0.57.0 // indirect
	golang.org/x/sync v0.22.0 // indirect
	golang.org/x/sys v0.47.0 // indirect
	golang.org/x/text v0.40.0 // indirect
	google.golang.org/genproto v0.0.0-20230410155749-daa745c078e1 // indirect
	google.golang.org/grpc v1.81.1 // indirect
	google.golang.org/protobuf v1.36.11 // indirect
)
