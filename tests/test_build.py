"""Regression checks for toolchain detection and the independent checker."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("k230_build", Path(__file__).resolve().parents[1] / "build.py")
build = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(build)


class ToolchainTests(unittest.TestCase):
    def setUp(self):
        self.allowed_root = (build.ROOT / ".build").resolve()
        self.allowed_root.mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="infrastructure-test-", dir=self.allowed_root)
        self.root = Path(self.temp.name).resolve()
        self.work = self.root / ".build"
        self.work.mkdir()
        self.root_patch = patch.object(build, "ROOT", self.root)
        self.root_patch.start()

    def tearDown(self):
        self.root_patch.stop()
        assert self.root.is_relative_to(self.allowed_root)
        self.temp.cleanup()

    @patch.object(build.shutil, "which", return_value=None)
    @patch.object(build.subprocess, "check_output", return_value="The Rocq Prover, version 9.1.0\ncompiled with OCaml 4.14.2")
    def test_native_probe_does_not_invent_package_version(self, version, which):
        with patch.object(build.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "Injective : ...\n")):
            result = build.check_toolchain(str(self.root / "coqc"), self.work, {})
        self.assertIsNone(result["detected_stdlib_version"])
        self.assertEqual(result["required_stdlib_version"], "9.0.0")
        self.assertIn("FinFun.Injective", (self.work / "ToolchainProbe.v").read_text())

    @patch.object(build.subprocess, "check_output", return_value="The Rocq Prover, version 9.1.1")
    def test_wrong_compiler_fails_before_compilation(self, version):
        with patch.object(build.subprocess, "run") as run:
            with self.assertRaisesRegex(RuntimeError, "requires Rocq 9.1.0"):
                build.check_toolchain("coqc", self.work, {})
            run.assert_not_called()

    @patch.object(build.shutil, "which", return_value=None)
    @patch.object(build.subprocess, "check_output", return_value="The Rocq Prover, version 9.1.0")
    def test_incompatible_stdlib_fails_with_diagnostic(self, version, which):
        with patch.object(build.subprocess, "run", return_value=subprocess.CompletedProcess([], 1, "FinFun.Injective not found")):
            with self.assertRaisesRegex(RuntimeError, "Install rocq-stdlib.9.0.0"):
                build.check_toolchain("coqc", self.work, {})

    def test_exact_opam_stdlib_required(self):
        compiler = str(self.root / "bin" / "coqc")
        env = {"OPAM_SWITCH_PREFIX": str(self.root)}
        with patch.object(build.shutil, "which", side_effect=lambda name, **kw: "opam" if name == "opam" else compiler):
            with patch.object(build.subprocess, "check_output", side_effect=["The Rocq Prover, version 9.1.0", "9.1.0"]):
                with self.assertRaisesRegex(RuntimeError, "found 9.1.0"):
                    build.check_toolchain(compiler, self.work, env, require_opam=True)

    @patch.object(build.shutil, "which", return_value=None)
    @patch.object(build.subprocess, "check_output", return_value="The Rocq Prover, version 9.1.0")
    def test_ci_requires_version_evidence(self, version, which):
        with self.assertRaisesRegex(RuntimeError, "active opam switch"):
            build.check_toolchain("coqc", self.work, {}, require_opam=True)

    def test_kernel_check_has_no_admitted_dependencies(self):
        seen = []

        def run(args, **kwargs):
            seen.extend(args)
            kwargs["stdout"].write("CONTEXT SUMMARY\n===============\n* Axioms: <none>\n")
            return subprocess.CompletedProcess(args, 0)

        with patch.object(build.subprocess, "check_output", return_value="The Rocq Proof Checker, version 9.1.0"):
            with patch.object(build.subprocess, "run", side_effect=run):
                result = build.check_kernel("coqc", "coqchk", ["-Q", "src", "K230"], self.work, {})
        self.assertEqual(result["status"], "PASSED")
        self.assertEqual(result["exit_code"], 0)
        self.assertEqual(json.loads((self.work / "coqchk-result.json").read_text())["exit_code"], 0)
        self.assertEqual(seen[-1], "K230.Correct230")
        self.assertNotIn("-admit", seen)
        self.assertNotIn("-norec", seen)

    def test_kernel_failure_is_not_success(self):
        def run(args, **kwargs):
            kwargs["stdout"].write("Modules were successfully checked\nError: inconsistent assumptions\n")
            return subprocess.CompletedProcess(args, 1)

        with patch.object(build.subprocess, "check_output", return_value="The Rocq Proof Checker, version 9.1.0"):
            with patch.object(build.subprocess, "run", side_effect=run):
                with self.assertRaisesRegex(RuntimeError, "kernel recheck failed"):
                    build.check_kernel("coqc", "coqchk", [], self.work, {})
        self.assertEqual(json.loads((self.work / "coqchk-result.json").read_text())["exit_code"], 1)


if __name__ == "__main__":
    unittest.main()
