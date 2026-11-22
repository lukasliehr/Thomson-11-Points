#!/usr/bin/env python3
"""Unpack the certificate modules and compare them with the manifest.

    python3 Certificates/unpack.py            unpack every `*.lean.xz` below Certificates/, then check all modules
    python3 Certificates/unpack.py --check    only check the modules against Certificates/MANIFEST.sha256
    python3 Certificates/unpack.py --clean    remove the unpacked modules again

The data modules of the certificates are stored as `<name>.lean.xz`. Lean needs them as `<name>.lean` in the
same folder; this program writes these files. `MANIFEST.sha256` holds the SHA-256 of every Lean module below
`Certificates/` (of a data module in its unpacked form), in the format of `sha256sum`. The program needs
Python 3 and its standard library only. The option `--jobs N` sets the number of processes (default: all cores).
"""
import argparse
import hashlib
import lzma
import os
import sys
from concurrent.futures import ProcessPoolExecutor

ROOT = os.path.dirname(os.path.abspath(__file__))
MANIFEST = os.path.join(ROOT, "MANIFEST.sha256")


def read_manifest():
    entries = {}
    with open(MANIFEST, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if line:
                digest, path = line.split("  ", 1)
                entries[path] = digest
    return entries


def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def unpack_one(job):
    """Write the module of one `.lean.xz` file unless it is there with the digest of the manifest."""
    rel, digest = job
    target = os.path.join(ROOT, rel)
    if os.path.exists(target) and sha256_of(target) == digest:
        return rel, "kept"
    with lzma.open(target + ".xz", "rb") as f:
        data = f.read()
    if hashlib.sha256(data).hexdigest() != digest:
        return rel, "MISMATCH"
    tmp = target + ".part"
    with open(tmp, "wb") as f:
        f.write(data)
    os.replace(tmp, target)
    return rel, "unpacked"


def check_one(job):
    rel, digest = job
    target = os.path.join(ROOT, rel)
    if not os.path.exists(target):
        return rel, "MISSING"
    return rel, "ok" if sha256_of(target) == digest else "MISMATCH"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true", help="only compare the modules with the manifest")
    ap.add_argument("--clean", action="store_true", help="remove the unpacked modules")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1, help="number of processes")
    args = ap.parse_args()

    manifest = read_manifest()
    packed = sorted(rel for rel in manifest if os.path.exists(os.path.join(ROOT, rel + ".xz")))

    if args.clean:
        removed = 0
        for rel in packed:
            target = os.path.join(ROOT, rel)
            if os.path.exists(target):
                os.remove(target)
                removed += 1
        print(f"removed {removed} unpacked modules")
        return 0

    bad = []
    with ProcessPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        if not args.check:
            counts = {}
            jobs = [(rel, manifest[rel]) for rel in packed]
            for k, (rel, state) in enumerate(pool.map(unpack_one, jobs, chunksize=8), 1):
                counts[state] = counts.get(state, 0) + 1
                if state == "MISMATCH":
                    bad.append((rel, state))
                if k % 500 == 0 or k == len(jobs):
                    print(f"  {k} of {len(jobs)} data modules", flush=True)
            print("data modules: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())))
        jobs = sorted(manifest.items())
        ok = 0
        for rel, state in pool.map(check_one, jobs, chunksize=8):
            if state == "ok":
                ok += 1
            else:
                bad.append((rel, state))
    print(f"modules of the manifest: {len(manifest)}; with the digest of the manifest: {ok}")
    for rel, state in bad[:20]:
        print(f"  {state}: {rel}", file=sys.stderr)
    if bad:
        print(f"FAILED: {len(bad)} modules are missing or differ from the manifest", file=sys.stderr)
        return 1
    print("all modules agree with the manifest")
    return 0


if __name__ == "__main__":
    sys.exit(main())
