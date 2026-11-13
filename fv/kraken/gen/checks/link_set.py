#!/usr/bin/env python3
"""The one link set of the Prysm target: prysm/go1.26.10/link-set.

Usage (Python 3 standard library only; run with python3 -I -B; every step runs gated):
  link_set.py functions                               print the functions of the link set (one per line)
  link_set.py filter <outdir> <objdump> <elf> <nm>    write <outdir>/target.objdump (the functions above, in
                                                      address order) and link the ELF and nm into <outdir>
  link_set.py data <outdir>                           after `convert_objdump.py <outdir>/target.objdump <outdir>/p1bin-amd64.nm
                                                      <outdir>/norm --norm`: write <outdir>/data/*.data
Then `link/check.py <outdir>` (a)-(f). The committed copy is fv/kraken/prysm/go1.26.10/link-set.

The function list is the union of the lists of the `gen/checks/*link.py` scripts. They locate the data items from the
operands of the converted code. `data` runs the `data` command of each script with <outdir> as its output directory
and as every link directory argument, so the items of all scripts come from the one set.
A data file id that two scripts write must get the same bytes; the command stops otherwise.
Exception to a fresh `convert_objdump.py --norm` run: the committed `…v1alpha1.Validator.MarshalSSZTo.S` keeps the unsigned form
`lea 0xffffff58(%rsp),%r12` of an older converter (see FINDINGS.md); no theorem uses its program constant.
"""
import pathlib
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import callgraph  # noqa: E402
import checkpoint_and_epoch_link  # noqa: E402

# script, number of link directory arguments of its `data` command, extra arguments
DATA_RUNS = [("checkpoint_and_epoch_link.py", 0, []), ("attestation_data_link.py", 1, []), ("beacon_block_header_link.py", 2, []), ("eth1_data_link.py", 2, []),
             ("flat_encoders_link.py", 2, []), ("flat_types_link.py", 3, []), ("blob_identifier_and_deposit_message_link.py", 2, []), ("deposit_data_and_pending_partial_withdrawal_link.py", 2, []),
             ("pending_consolidation_and_sync_committee_message_link.py", 2, []), ("seven_flat_decoders_link.py", 2, []), ("lists_and_vectors_link.py", 2, []), ("lists_and_vectors_link.py", 2, ["--with-indexed-attestation"]),
             ("historical_batch_link.py", 2, []), ("deposit_link.py", 2, []), ("data_columns_encoder_link.py", 2, []), ("data_columns_decoder_link.py", 2, [])]


def functions():
    import attestation_data_link, beacon_block_header_link, deposit_link, eth1_data_link, flat_encoders_link, data_columns_decoder_link, data_columns_encoder_link, flat_types_link  # noqa: E401
    import blob_identifier_and_deposit_message_link, deposit_data_and_pending_partial_withdrawal_link, pending_consolidation_and_sync_committee_message_link, seven_flat_decoders_link, historical_batch_link, lists_and_vectors_link  # noqa: E401
    out = list(callgraph.FUNCS)
    for m in (attestation_data_link, beacon_block_header_link, deposit_link, eth1_data_link, flat_encoders_link, flat_types_link, blob_identifier_and_deposit_message_link, deposit_data_and_pending_partial_withdrawal_link, pending_consolidation_and_sync_committee_message_link, seven_flat_decoders_link, historical_batch_link, lists_and_vectors_link):
        out += m.FUNCS
    out += [data_columns_encoder_link.TARGET, data_columns_decoder_link.TARGET]
    seen = []
    for f in out:
        if f not in seen:
            seen.append(f)
    return seen


def filt(outdir, objdump, elf, nm):
    checkpoint_and_epoch_link.callgraph.FUNCS = functions()
    return checkpoint_and_epoch_link.filt(outdir, objdump, elf, nm)


def data(outdir):
    out = pathlib.Path(outdir)
    (out / "data").mkdir(exist_ok=True)
    written = {}
    for script, ndirs, extra in DATA_RUNS:
        with tempfile.TemporaryDirectory() as d:
            t = pathlib.Path(d)
            for name in ("norm", "target.objdump", "p1bin-amd64", "p1bin-amd64.nm"):
                (t / name).symlink_to((out / name).resolve())
            (t / "data").mkdir()
            r = subprocess.run([sys.executable, "-I", "-B", str(HERE / script), "data", str(t)]
                               + [str(out)] * ndirs + extra, capture_output=True, text=True)
            if r.returncode != 0:
                print(r.stdout + r.stderr)
                print(f"FAIL {script} {' '.join(extra)}: exit {r.returncode}")
                return 1
            for p in sorted((t / "data").glob("*.data")):
                b = p.read_bytes()
                if written.setdefault(p.name, (b, script))[0] != b:
                    print(f"FAIL {p.name}: {script} and {written[p.name][1]} write different bytes")
                    return 1
                # a later script reads the items of an earlier one from <outdir>/data (for example data_columns_encoder_link.py)
                (out / "data" / p.name).write_bytes(b)
            print(f"{script} {' '.join(extra)}: {len(list((t / 'data').glob('*.data')))} data files")
    print(f"data files {len(written)}")
    return 0


if __name__ == "__main__":
    c = sys.argv[1] if len(sys.argv) > 1 else ""
    if c == "functions":
        print("\n".join(functions()))
        sys.exit(0)
    if c == "filter":
        sys.exit(filt(*sys.argv[2:6]))
    if c == "data":
        sys.exit(data(sys.argv[2]))
    sys.exit(__doc__)
