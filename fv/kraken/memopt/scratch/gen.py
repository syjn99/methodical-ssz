"""Generate the M2 diagnostic copies of Fk/WitLcM4x16.lean.

Run from fv/kraken/lean: python3 ../memopt/scratch/gen.py
The source is the original (`by decide`) file, read from git at the base
commit 86fd060, not the working tree (which has the M3 `simp` proofs).
Line numbers refer to that file (same as at daa9dbc).
"""
import pathlib
import subprocess

BASE = "86fd060:fv/kraken/lean/Fk/WitLcM4x16.lean"
SRC = subprocess.run(["git", "show", BASE], check=True, capture_output=True,
                     text=True).stdout.splitlines()
OUT = pathlib.Path(__file__).parent
END = "end Fk.WitLcM4x16"


def lines(a, b):  # 1-based, inclusive
    return SRC[a - 1:b]


def write(name, body):
    (OUT / f"{name}.lean").write_text("\n".join(body) + "\n")


def after_imports(body, opt):  # options must follow the import block
    return body[:3] + [opt] + body[3:]


HEAD = lines(1, 43)        # imports .. u64nil
U64V0 = lines(44, 46)
U64V = lines(44, 55)       # u64v0 .. u64v3
DEFS = lines(56, 63)       # block, mem, s0
FULL = lines(1, 106)
STMT = SRC[44].split(" := by decide")[0]  # "theorem u64v0 : ... = [...]"
assert STMT.startswith("theorem u64v0 :") and SRC[105] == END

# A: declaration boundaries
write("A0", HEAD + [END])  # header only
write("A1", HEAD + U64V0 + [END])
write("A2", HEAD + U64V + [END])
write("A3", HEAD + U64V + DEFS + [END])
write("A4", FULL)

# B: parallelism
write("B1", after_imports(FULL, "set_option Elab.async false"))

# C: proof method for u64v0 (statement unchanged)
HB = "set_option maxHeartbeats 4000000 in"
write("C0", HEAD + U64V0 + [END])  # = A1, by decide
write("C1", HEAD + [HB, STMT + " := by decide +kernel", END])
write("C2", HEAD + [HB, STMT + " := by rfl", END])
write("C3", HEAD + [HB, STMT + " := by simp [u64Bytes, EthLib.Serialization.Ssz.uintBytes]", END])
LEMMAS = [
    "theorem m2_uintBytes_succ (w v : Nat) :",
    "    (EthLib.Serialization.Ssz.uintBytes (w + 1) v).toList = UInt8.ofNat (v % 256) :: (EthLib.Serialization.Ssz.uintBytes w (v / 256)).toList := by",
    "  simp [EthLib.Serialization.Ssz.uintBytes]",
    "",
    "theorem m2_u64Bytes_toList (l : List UInt64) :",
    "    (u64Bytes l).toList = l.flatMap (fun x => (EthLib.Serialization.Ssz.uintBytes 8 x.toNat).toList) := by",
    "  induction l with",
    "  | nil => rfl",
    "  | cons x xs ih => simp [u64Bytes, ih]",
    "",
]
write("C4", HEAD + LEMMAS + [HB, STMT + " := by rw [m2_u64Bytes_toList]; decide", END])
write("C5", HEAD + LEMMAS + [HB, STMT + " := by",
                             "  simp only [m2_u64Bytes_toList, List.flatMap_cons, List.flatMap_nil, m2_uintBytes_succ]",
                             "  decide", END])
# C6: elaboration only (kernel check skipped; diagnostic, no proof term trusted)
write("C6", after_imports(HEAD + U64V0 + [END], "set_option debug.skipKernelTC true"))
write("C7", after_imports(HEAD + U64V + [END], "set_option debug.skipKernelTC true"))

# D: no code generation for the big definitions
NC = FULL[:]
for i, s in enumerate(NC):
    for d in ("def objs ", "def block ", "def mem ", "def s0 "):
        if s.startswith(d):
            NC[i] = "noncomputable " + s
write("D1", NC)

# E: size scaling of one u64Bytes decide
for n in (1, 4, 8, 12, 16):
    xs = list(range(1, n + 1))
    bs = [b for x in xs for b in [x] + [0] * 7]
    write(f"E{n}", HEAD + [HB, f"theorem u64e : (u64Bytes {xs}).toList = {bs} := by decide", END])

# C8, C9: the full file with a different u64v proof (scratch only, not an M3 change)
LIST_PROOF = " := by rw [m2_u64Bytes_toList]; decide"
C8 = FULL[:43] + LEMMAS + [s.replace(" := by decide", LIST_PROOF) if s.startswith("theorem u64v") else s
                            for s in FULL[43:]]
write("C8", C8)
C9 = [s.split(" := by decide")[0] + " := u64v0" if s.startswith(("theorem u64v1", "theorem u64v2", "theorem u64v3")) else s
      for s in FULL]
write("C9", C9)
SIMP_PROOF = " := by simp [u64Bytes, EthLib.Serialization.Ssz.uintBytes]"
write("C10", [s.replace(" := by decide", SIMP_PROOF) if s.startswith("theorem u64v") else s for s in FULL])
