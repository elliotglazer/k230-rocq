"""Rebuild K230 with Rocq 9.1.0 and rocq-stdlib 9.0.0."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
COMPILER_VERSION = "9.1.0"
STDLIB_VERSION = "9.0.0"
KERNEL_TARGET = "K230.Correct230"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def below(root, relative):
    path = (root / relative).resolve()
    require(path.is_relative_to(root.resolve()), f"Path escapes its root: {relative}")
    return path


def compiler_environment(coqc):
    env = dict(os.environ)
    if os.name == "nt":
        library = subprocess.check_output([coqc, "-where"], text=True).strip()
        try:
            relative_library = os.path.relpath(library, ROOT)
        except ValueError as exc:
            raise RuntimeError("On Windows, put this checkout on the same drive as Rocq.") from exc
        env.update(COQLIB=relative_library, ROCQLIB=relative_library)
    return env


def check_toolchain(coqc, work, env, require_opam=False):
    version = subprocess.check_output([coqc, "--version"], text=True, env=env).strip()
    require(re.search(r"version 9\.1\.0(?:\s|$)", version) is not None,
            f"This build requires Rocq {COMPILER_VERSION}; found: {version}")
    installed_stdlib = None
    # Only query opam when this compiler belongs to its active switch.
    # Native Platform installations have no opam package database.
    switch = env.get("OPAM_SWITCH_PREFIX")
    opam = shutil.which("opam", path=env.get("PATH"))
    compiler_path = Path(shutil.which(coqc, path=env.get("PATH")) or coqc).resolve()
    if switch and opam and compiler_path.is_relative_to(Path(switch).resolve()):
        installed_stdlib = subprocess.check_output(
            [opam, "list", "--installed", "--short", "--columns=version", "--color=never", "rocq-stdlib"],
            text=True, env=env).strip()
        require(installed_stdlib == STDLIB_VERSION,
                f"Install rocq-stdlib.{STDLIB_VERSION}; found {installed_stdlib or 'no package'}.")
    require(not require_opam or installed_stdlib == STDLIB_VERSION,
            "--require-opam-stdlib needs the selected compiler in an active opam switch.")
    probe = work / "ToolchainProbe.v"
    probe.write_text("From Stdlib Require Import FinFun.\nCheck FinFun.Injective.\n", encoding="utf-8")
    run = subprocess.run([coqc, str(probe.relative_to(ROOT))], cwd=ROOT, env=env,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, encoding="utf-8", errors="replace")
    (work / "toolchain.log").write_text(run.stdout, encoding="utf-8")
    require(run.returncode == 0,
            f"Standard-library compatibility check failed. Install rocq-stdlib.{STDLIB_VERSION}.\n{run.stdout}")
    result = {"status": "PASSED", "compiler_version": version,
              "required_stdlib_version": STDLIB_VERSION,
              "detected_stdlib_version": installed_stdlib,
              "stdlib_check": "opam package version and API probe" if installed_stdlib else "API probe only; packaged installation has no opam version record"}
    (work / "toolchain-result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return result


def check_kernel(coqc, requested, flags, work, env):
    sibling = Path(coqc).resolve().with_name("coqchk.exe" if os.name == "nt" else "coqchk")
    command = requested or (str(sibling) if sibling.is_file() else shutil.which("coqchk"))
    require(command, "coqchk was requested but not found; pass --coqchk-command /path/to/coqchk.")
    version = subprocess.check_output([command, "--version"], text=True, env=env).strip()
    require(re.search(r"(?:version\s+)?9\.1\.0(?:\s|$)", version) is not None,
            f"coqchk must match Rocq {COMPILER_VERSION}; found: {version}")
    started = time.perf_counter()
    with (work / "coqchk.log").open("w", encoding="utf-8") as log:
        run = subprocess.run([command, *flags, "-silent", "-o", KERNEL_TARGET],
                             cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    # Rocq 9.1.0 suppresses the success sentence in -silent mode. The
    # checker's exit status is authoritative; record it even on failure.
    result = {"status": "PASSED" if run.returncode == 0 else "FAILED",
              "target": KERNEL_TARGET, "exit_code": run.returncode,
              "compiler_version": version, "seconds": time.perf_counter() - started,
              "log_sha256": sha(work / "coqchk.log")}
    (work / "coqchk-result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    require(run.returncode == 0,
            "Independent kernel recheck failed; see .build/coqchk.log.")
    return result


def check_machine(manifest):
    machine = ROOT / "machine/k230.tm"
    require(sha(machine) == manifest["machine_sha256"], "Machine hash mismatch")
    require(sha(ROOT / "machine/sites230.json") == manifest["sites_sha256"], "Program-sites hash mismatch")
    table, start = {}, None
    for line in machine.read_text(encoding="utf-8").splitlines():
        if line.startswith("#! start "):
            start = int(line.split()[-1])
        if not line or line.startswith("#"):
            continue
        q, r, w, direction, nxt = line.split()
        key = int(q), int(r)
        require(key not in table, f"Duplicate transition: {key}")
        require(int(w) in (0, 1) and direction in ("L", "R") and 0 <= int(nxt) <= 230,
                f"Invalid transition: {line}")
        table[key] = int(w), direction, int(nxt)
    require(start == 0, "Wrong initial state")
    require(set(table) == {(q, r) for q in range(230) for r in (0, 1)}, "Incomplete transition table")
    source = (ROOT / "coq/tm/Table230.v").read_text(encoding="utf-8")
    rows = re.findall(r"\((true|false), ([LR]), (\d+), (true|false), ([LR]), (\d+)\)", source)
    require(len(rows) == 230, "Wrong Rocq table size")
    for q, (w, d, n, w1, d1, n1) in enumerate(rows):
        require(table[q, 0] == (int(w == "true"), d, int(n)), f"Table mismatch at {q},0")
        require(table[q, 1] == (int(w1 == "true"), d1, int(n1)), f"Table mismatch at {q},1")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT / ".deps/jeff-busy-beaver",
                        help="Existing checkout of the pinned upstream repository")
    parser.add_argument("--coqc", default=os.environ.get("COQC") or shutil.which("coqc"))
    parser.add_argument("--check-only", action="store_true", help="Check all source hashes and the table without compiling")
    parser.add_argument("--check-toolchain", action="store_true", help="Check the pinned compiler and stdlib API without rebuilding the proof")
    parser.add_argument("--require-opam-stdlib", action="store_true", help="Require an exact installed rocq-stdlib package version, as in CI")
    parser.add_argument("--coqchk", action="store_true", help="Independently kernel-check K230.Correct230 after the clean rebuild")
    parser.add_argument("--coqchk-command", help="Path to the coqchk executable matching the compiler")
    args = parser.parse_args()
    require(not (args.check_only and args.check_toolchain), "Choose only one check-only mode.")
    if args.check_toolchain:
        require(args.coqc, f"Set COQC or pass --coqc to select Rocq {COMPILER_VERSION}.")
        work = ROOT / ".build"
        work.mkdir(exist_ok=True)
        print(json.dumps(check_toolchain(args.coqc, work, compiler_environment(args.coqc), args.require_opam_stdlib), indent=2))
        return 0
    manifest_path = ROOT / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    reference = args.reference.resolve()
    for relative, digest in manifest["local_files"].items():
        require(sha(below(ROOT, relative)) == digest, f"Local source changed: {relative}")
    check_machine(manifest)
    require(reference.is_dir(), "Missing upstream checkout. Run python fetch_dependency.py first.")
    # Pin the bytes that enter the proof, so an extracted source archive works
    # as well as a Git checkout. fetch_dependency.py also checks Git's commit.
    commit = manifest["reference"]["commit"]
    for item in manifest["reference_files"].values():
        require(sha(below(reference, item["source"])) == item["sha256"],
                f"Upstream source changed: {item['source']}")
    if args.check_only:
        print(f"All {len(manifest['compile_order'])} proof-source hashes and all 460 transitions match.")
        return 0
    require(args.coqc, f"Set COQC or pass --coqc to select Rocq {COMPILER_VERSION}.")

    # Work on byte-identical copies. No compiled objects are read from upstream
    # or from the checked-in source directories, and every source is recompiled.
    work = ROOT / ".build"
    work.mkdir(exist_ok=True)
    env = compiler_environment(args.coqc)
    toolchain = check_toolchain(args.coqc, work, env, args.require_opam_stdlib)
    local_work = work / "project"
    for relative in manifest["local_files"]:
        if not relative.endswith(".v"):
            continue
        dest = below(local_work, relative)
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, dest)
    for relative, item in manifest["reference_files"].items():
        dest = below(ROOT, relative)
        require(dest.is_relative_to(work), "Upstream build destination is outside .build")
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(reference / item["source"], dest)

    def compiled_path(relative):
        return relative if relative in manifest["reference_files"] else ".build/project/" + relative

    flags = []
    for name, relative in manifest["logical_roots"].items():
        build_root = relative if relative.startswith(".build/library/") else ".build/project/" + relative
        flags.extend(["-Q", build_root, name])
    started = time.perf_counter()
    result = {"status": "RUNNING", "compiler_version": toolchain["compiler_version"], "toolchain": toolchain,
              "manifest_sha256": sha(manifest_path), "machine_sha256": manifest["machine_sha256"],
              "reference_commit": commit, "compiled": [], "closed_reports": 0}
    try:
        with (work / "verification.log").open("w", encoding="utf-8") as log:
            for relative in manifest["compile_order"]:
                options = ["-w", "-deprecated,-notation-overridden"]
                if relative.startswith(".build/library/Undecidability/"):
                    options += ["-set", "Default Proof Using = Type"]
                run = subprocess.run([args.coqc, *flags, *options, compiled_path(relative)],
                                     cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
                log.write(f"FILE {relative}\n{run.stdout}\n")
                log.flush()
                print(f"{run.returncode}: {relative}", flush=True)
                require(run.returncode == 0, run.stdout)
                result["compiled"].append(relative)
                if relative == manifest["target"]:
                    result["closed_reports"] = run.stdout.count("Closed under the global context")
                    require(result["closed_reports"] == manifest["expected_closed_reports"]
                            and "Axioms:" not in run.stdout, "Final assumption audit failed")
        require(result["closed_reports"] == manifest["expected_closed_reports"], "Final audit was not compiled")
        for relative, digest in manifest["local_files"].items():
            require(sha(ROOT / relative) == digest, f"Source changed during build: {relative}")
            if relative.endswith(".v"):
                require(sha(local_work / relative) == digest, f"Build copy changed: {relative}")
        for relative, item in manifest["reference_files"].items():
            require(sha(ROOT / relative) == item["sha256"], f"Dependency build copy changed: {relative}")
        if args.coqchk:
            print(f"Independent kernel recheck: {KERNEL_TARGET}", flush=True)
            result["coqchk"] = check_kernel(args.coqc, args.coqchk_command, flags, work, env)
        result["status"] = "PASSED"
    except Exception as exc:
        result.update(status="FAILED", error=str(exc))
    result["seconds"] = time.perf_counter() - started
    (work / "verification-result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "compiled"}, indent=2))
    return 0 if result["status"] == "PASSED" else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"Build error: {error}", file=sys.stderr)
        sys.exit(1)
