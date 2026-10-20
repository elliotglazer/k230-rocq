"""Rebuild the classical PA-provability proof separately from the axiom-free proof."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import time

CLASSICAL = Path(__file__).resolve().parent
ROOT = CLASSICAL.parent
WORK = ROOT / ".build/classical"
TARGET = "PAModel.PALiteralZFCConsistency"
MACHINE_SHA256 = "e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8"
ALLOWED_AXIOMS = frozenset({
    "Classical_Prop.classic",
    "ClassicalUniqueChoice.dependent_unique_choice",
    "RelationalChoice.relational_choice",
})
AUDITED_THEOREMS = (
    "p230_actual_normal_search",
    "p230_actual_counter_search_equivalence",
    "literal230_nonhalting_ZFC_consistency",
    "PA_proves_literal230_ZFC_consistency",
)
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
DIGEST = re.compile(r"[0-9a-f]{64}\Z")

# Share the published machine and toolchain checks, without importing any .vo.
SPEC = importlib.util.spec_from_file_location("k230_axiom_free_build", ROOT / "build.py")
shared = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(shared)
require, sha = shared.require, shared.sha


def safe_relative(value):
    """Require portable relative manifest paths on both Windows and Linux."""
    require(isinstance(value, str) and value, "Empty or non-string source path")
    require("\\" not in value and ":" not in value, f"Non-portable source path: {value}")
    path = PurePosixPath(value)
    require(not path.is_absolute() and all(p not in ("", ".", "..") for p in value.split("/")),
            f"Path escapes its root or is not normalized: {value}")
    return path


def bounded(root, relative):
    path = (root / Path(safe_relative(relative))).resolve()
    require(path.is_relative_to(root.resolve()), f"Path escapes its root: {relative}")
    return path


def validate_manifest(manifest):
    """Check logical names, the source map, and the complete dependency order."""
    require(manifest.get("format_version") == 1, "Unsupported classical manifest format")
    require(manifest.get("target") == TARGET, "Unexpected classical proof target")
    require(manifest.get("machine_sha256") == MACHINE_SHA256, "Unexpected machine hash")
    axioms = manifest.get("allowed_axioms", [])
    require(len(axioms) == len(ALLOWED_AXIOMS) and set(axioms) == ALLOWED_AXIOMS,
            "The classical axiom allowlist must be the published three axioms")
    roots = manifest.get("logical_roots", {})
    require(isinstance(roots, dict) and roots, "Missing logical roots")
    for name, path in roots.items():
        require(MODULE.fullmatch(name) is not None, f"Invalid logical root: {name}")
        require(safe_relative(path).parts[0] == "src", f"Logical root is outside src: {path}")
    require(len(set(roots.values())) == len(roots), "Duplicate logical root paths")
    sources = manifest.get("sources", {})
    order = manifest.get("compile_order", [])
    require(isinstance(sources, dict) and sources, "Missing proof sources")
    require(isinstance(order, list) and len(order) == len(set(order))
            and set(order) == set(sources), "Compile order must list every module exactly once")
    require(TARGET in sources, "Final proof target is missing")
    positions = {name: i for i, name in enumerate(order)}
    destinations = set()
    for name, item in sources.items():
        require(MODULE.fullmatch(name) is not None, f"Invalid logical module: {name}")
        require(item.get("kind") in {"local", "shared", "reference"}, f"Invalid source kind: {name}")
        require(safe_relative(item.get("path")).suffix == ".v", f"Not a source file: {name}")
        require(DIGEST.fullmatch(item.get("sha256", "")) is not None, f"Invalid source hash: {name}")
        destination = safe_relative(item.get("destination"))
        matches = [root for root in roots if name == root or name.startswith(root + ".")]
        require(matches, f"No logical root for {name}")
        root = max(matches, key=len)
        suffix = name[len(root):].lstrip(".")
        require(suffix, f"Module equals its directory namespace: {name}")
        expected = PurePosixPath(roots[root]) / (suffix.replace(".", "/") + ".v")
        require(destination == expected, f"Source destination does not match logical module: {name}")
        require(str(destination).casefold() not in destinations, f"Duplicate source destination: {destination}")
        destinations.add(str(destination).casefold())
        dependencies = item.get("dependencies")
        require(isinstance(dependencies, list) and len(dependencies) == len(set(dependencies)),
                f"Invalid dependency list: {name}")
        for dependency in dependencies:
            require(dependency in sources, f"Unpackaged dependency {dependency} of {name}")
            require(positions[dependency] < positions[name], f"Dependency is out of order: {dependency} -> {name}")
    return manifest


def source_path(item, reference):
    return bounded({"local": CLASSICAL, "shared": ROOT, "reference": reference}[item["kind"]], item["path"])


def check_inputs(manifest, reference, manifest_digest=None, copies=False):
    root_manifest = json.loads((ROOT / "manifest.json").read_text(encoding="utf-8"))
    require(manifest["reference"] == root_manifest["reference"], "Classical and axiom-free upstream pins differ")
    require(root_manifest["machine_sha256"] == manifest["machine_sha256"], "The two builds select different machines")
    shared.check_machine(root_manifest)
    require(reference.is_dir(), "Missing upstream checkout. Run python fetch_dependency.py first.")
    if manifest_digest is not None:
        require(sha(CLASSICAL / "manifest.json") == manifest_digest, "Classical manifest changed during the build")
    for name, item in manifest["sources"].items():
        require(sha(source_path(item, reference)) == item["sha256"], f"Source hash mismatch: {name}")
        if copies:
            require(sha(bounded(WORK, item["destination"])) == item["sha256"], f"Build-copy hash mismatch: {name}")


def parse_assumptions(output):
    """Read the four Print Assumptions reports emitted by the frozen endpoint."""
    blocks = re.split(r"(?m)^Axioms:\s*$", output)
    require(len(blocks) == 5 and "Closed under the global context" not in output,
            "Expected exactly four classical Print Assumptions reports")
    reports = []
    for block in blocks[1:]:
        # Axiom names begin in column zero. Their multiline types are indented.
        names = re.findall(r"(?m)^([^\s:]+)\s*(?=:)", block)
        require(names and len(names) == len(set(names)), "Missing or duplicate axiom in assumption report")
        unexpected = set(names) - ALLOWED_AXIOMS
        require(not unexpected, "Unexpected axiom(s): " + ", ".join(sorted(unexpected)))
        reports.append(frozenset(names))
    expected = [frozenset({"Classical_Prop.classic"})] * 2 + [ALLOWED_AXIOMS] * 2
    require(reports == expected, "Endpoint assumption sets differ from the published four-theorem audit")
    return {name: sorted(axioms) for name, axioms in zip(AUDITED_THEOREMS, reports)}


def prepare_work():
    """Remove only this builder's previous source copies and per-module logs."""
    expected = ROOT.resolve() / ".build" / "classical"
    require(WORK.resolve() == expected, "Classical build path resolves outside its own directory")
    require(not (ROOT / ".build").is_symlink() and not WORK.is_symlink(), "Refusing a symlinked build directory")
    WORK.mkdir(parents=True, exist_ok=True)
    for name in ("src", "logs"):
        directory = WORK / name
        require(not directory.is_symlink() and directory.resolve().parent == WORK.resolve(),
                f"Refusing an unsafe build directory: {directory}")
        if directory.exists():
            shutil.rmtree(directory)
        directory.mkdir()
    for name in ("coqchk.log", "coqchk-result.json"):
        path = WORK / name
        require(not path.is_symlink(), f"Refusing a symlinked report: {path}")
        if path.exists():
            path.unlink()


def copy_sources(manifest, reference):
    for item in manifest["sources"].values():
        destination = bounded(WORK, item["destination"])
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source_path(item, reference), destination)
        require(sha(destination) == item["sha256"], f"Source copy changed: {item['destination']}")


def logical_flags(manifest):
    flags = []
    for namespace, directory in manifest["logical_roots"].items():
        flags.extend(["-Q", str(bounded(WORK, directory).relative_to(ROOT)), namespace])
    return flags


def compile_one(name, item, command, flags, env):
    options = ["-w", "-deprecated,-notation-overridden"]
    if name.split(".")[0] in {"Undecidability", "OldUndecidability"}:
        options += ["-set", "Default Proof Using = Type"]
    source = bounded(WORK, item["destination"])
    started = time.perf_counter()
    run = subprocess.run([command, *flags, *options, str(source.relative_to(ROOT))],
                         cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, encoding="utf-8", errors="replace")
    log = WORK / "logs" / (name + ".log")
    log.write_text(run.stdout, encoding="utf-8")
    entry = {"module": name, "exit_code": run.returncode, "seconds": time.perf_counter() - started,
             "log": str(log.relative_to(WORK)).replace("\\", "/"), "log_sha256": sha(log)}
    if run.returncode == 0:
        require(source.with_suffix(".vo").is_file(), f"Compiler produced no object: {name}")
        entry["object_sha256"] = sha(source.with_suffix(".vo"))
    return entry, run.stdout


def compile_sources(manifest, command, flags, env, jobs, result):
    pending = list(manifest["compile_order"])
    completed, running = set(), {}
    failed = None
    with (WORK / "verification.log").open("w", encoding="utf-8") as log:
        # Dependency edges, rather than order alone, decide which jobs can overlap.
        with ThreadPoolExecutor(max_workers=jobs) as executor:
            while pending or running:
                if failed is None:
                    ready = [name for name in pending
                             if set(manifest["sources"][name]["dependencies"]) <= completed]
                    for name in ready[:jobs - len(running)]:
                        pending.remove(name)
                        future = executor.submit(compile_one, name, manifest["sources"][name], command, flags, env)
                        running[future] = name
                require(running or not pending or failed is not None, "No compilable module remains in the dependency graph")
                if not running:
                    break
                done, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in done:
                    name = running.pop(future)
                    try:
                        entry, output = future.result()
                        result["compiled"].append(entry)
                        log.write(f"MODULE {name}\n{output}\n")
                        log.flush()
                        print(f"{entry['exit_code']}: {name}", flush=True)
                        if entry["exit_code"]:
                            failed = failed or f"Compilation failed for {name}; see .build/classical/{entry['log']}\n{output}"
                        else:
                            completed.add(name)
                            if name == TARGET:
                                result["assumption_reports"] = parse_assumptions(output)
                    except Exception as exc:
                        failed = failed or str(exc)
            require(failed is None, failed)
    require(completed == set(manifest["sources"]), "Some packaged modules were not compiled")
    require(result.get("assumption_reports"), "Final assumption audit was not compiled")


def check_kernel(coqc, requested, flags, env):
    resolved = Path(shutil.which(coqc, path=env.get("PATH")) or coqc).resolve()
    sibling = resolved.with_name("coqchk.exe" if os.name == "nt" else "coqchk")
    command = requested or (str(sibling) if sibling.is_file() else shutil.which("coqchk", path=env.get("PATH")))
    require(command, "coqchk was requested but not found; pass --coqchk-command.")
    version = subprocess.check_output([command, "--version"], text=True, env=env).strip()
    require(re.search(r"(?:version\s+)?9\.1\.0(?:\s|$)", version) is not None,
            f"coqchk must match Rocq {shared.COMPILER_VERSION}; found: {version}")
    started = time.perf_counter()
    with (WORK / "coqchk.log").open("w", encoding="utf-8") as log:
        run = subprocess.run([command, *flags, "-silent", "-o", TARGET],
                             cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    # -silent suppresses the success sentence. Trust the checker exit code.
    result = {"status": "PASSED" if run.returncode == 0 else "FAILED", "target": TARGET,
              "exit_code": run.returncode, "compiler_version": version,
              "seconds": time.perf_counter() - started, "log_sha256": sha(WORK / "coqchk.log")}
    (WORK / "coqchk-result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    require(run.returncode == 0, "Independent kernel recheck failed; see .build/classical/coqchk.log")
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT / ".deps/jeff-busy-beaver")
    parser.add_argument("--coqc", default=os.environ.get("COQC") or shutil.which("coqc"))
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--check-only", action="store_true", help="Check source hashes, source maps and machine without compiling")
    modes.add_argument("--check-toolchain", action="store_true", help="Check the pinned compiler and stdlib without rebuilding")
    parser.add_argument("--require-opam-stdlib", action="store_true", help="Require exact rocq-stdlib.9.0.0 package evidence, as in CI")
    parser.add_argument("--coqchk", action="store_true", help="Independently recheck the full classical endpoint and its dependencies")
    parser.add_argument("--coqchk-command", help="Path to the matching coqchk executable")
    parser.add_argument("--jobs", type=int, default=1, help="Maximum simultaneous compilations, following dependency edges")
    args = parser.parse_args(argv)
    require(args.jobs >= 1, "--jobs must be positive")
    require(WORK.resolve() == ROOT.resolve() / ".build/classical", "Unsafe classical build directory")
    require(not (ROOT / ".build").is_symlink() and not WORK.is_symlink(), "Refusing a symlinked build directory")
    WORK.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    result = {"status": "RUNNING", "target": TARGET, "machine_sha256": MACHINE_SHA256,
              "mode": "check-toolchain" if args.check_toolchain else "check-only" if args.check_only else "build",
              "coqchk_requested": args.coqchk, "jobs": args.jobs, "compiled": []}
    try:
        if args.check_toolchain:
            require(args.coqc, f"Set COQC or pass --coqc to select Rocq {shared.COMPILER_VERSION}")
            result["toolchain"] = shared.check_toolchain(args.coqc, WORK, shared.compiler_environment(args.coqc), args.require_opam_stdlib)
        else:
            manifest_path = CLASSICAL / "manifest.json"
            manifest_digest = sha(manifest_path)
            manifest = validate_manifest(json.loads(manifest_path.read_text(encoding="utf-8")))
            result.update(manifest_sha256=manifest_digest, reference_commit=manifest["reference"]["commit"])
            reference = args.reference.resolve()
            check_inputs(manifest, reference, manifest_digest)
            result["source_count"] = len(manifest["sources"])
            if not args.check_only:
                require(args.coqc, f"Set COQC or pass --coqc to select Rocq {shared.COMPILER_VERSION}")
                prepare_work()
                env = shared.compiler_environment(args.coqc)
                result["toolchain"] = shared.check_toolchain(args.coqc, WORK, env, args.require_opam_stdlib)
                copy_sources(manifest, reference)
                flags = logical_flags(manifest)
                compile_sources(manifest, args.coqc, flags, env, args.jobs, result)
                check_inputs(manifest, reference, manifest_digest, copies=True)
                if args.coqchk:
                    print(f"Independent kernel recheck: {TARGET}", flush=True)
                    result["coqchk"] = check_kernel(args.coqc, args.coqchk_command, flags, env)
                check_inputs(manifest, reference, manifest_digest, copies=True)
            result["input_hashes_checked"] = True
        result["status"] = "PASSED"
    except (Exception, KeyboardInterrupt) as exc:
        result.update(status="FAILED", error="Build interrupted" if isinstance(exc, KeyboardInterrupt) else str(exc))
    result["seconds"] = time.perf_counter() - started
    (WORK / "verification-result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "compiled"}, indent=2))
    return 0 if result["status"] == "PASSED" else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"Classical build error: {error}", file=sys.stderr)
        sys.exit(1)
