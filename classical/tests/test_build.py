"""Tests for the classical build's proof boundary and source-map checks."""
from contextlib import contextmanager
import importlib.util
import json
from pathlib import Path
import subprocess
import shutil
import unittest
from unittest.mock import patch
import uuid

SPEC = importlib.util.spec_from_file_location("k230_classical_build", Path(__file__).resolve().parents[1] / "build.py")
build = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(build)


@contextmanager
def scratch_directory():
    # mkdir's inherited ACL also permits subprocesses in Windows sandboxes.
    # TemporaryDirectory's private ACL can exclude the sandbox's process token.
    allowed = (build.ROOT / ".build").resolve()
    allowed.mkdir(exist_ok=True)
    path = allowed / ("classical-test-" + uuid.uuid4().hex)
    path.mkdir()
    try:
        yield path
    finally:
        assert path.resolve().parent == allowed
        shutil.rmtree(path)


def assumptions_output():
    classic = "Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n"
    choice = ("Axioms:\nRelationalChoice.relational_choice\n"
              "  : forall (A B : Type) (R : A -> B -> Prop), Prop\n"
              "ClassicalUniqueChoice.dependent_unique_choice\n"
              "  : forall (A : Type), Prop\n"
              "Classical_Prop.classic : forall P : Prop, P \\/ ~ P\n")
    return "Some harmless compiler output\n" + classic * 2 + choice * 2


def manifest():
    return {
        "format_version": 1,
        "target": build.TARGET,
        "machine_sha256": build.MACHINE_SHA256,
        "allowed_axioms": sorted(build.ALLOWED_AXIOMS),
        "logical_roots": {"PAModel": "src/PAModel"},
        "sources": {
            "PAModel.Base": {"kind": "local", "path": "coq/Base.v", "sha256": "a" * 64,
                             "destination": "src/PAModel/Base.v", "dependencies": []},
            build.TARGET: {"kind": "local", "path": "coq/PALiteralZFCConsistency.v", "sha256": "b" * 64,
                           "destination": "src/PAModel/PALiteralZFCConsistency.v", "dependencies": ["PAModel.Base"]},
        },
        "compile_order": ["PAModel.Base", build.TARGET],
    }


class AssumptionAuditTests(unittest.TestCase):
    def test_expected_classical_dependencies_are_recorded_per_theorem(self):
        result = build.parse_assumptions(assumptions_output())
        self.assertEqual(result[build.AUDITED_THEOREMS[0]], ["Classical_Prop.classic"])
        self.assertEqual(set(result[build.AUDITED_THEOREMS[-1]]), build.ALLOWED_AXIOMS)

    def test_unexpected_axiom_in_final_theorem_is_rejected(self):
        output = assumptions_output() + "Hidden.assumption : False\n"
        with self.assertRaisesRegex(RuntimeError, "Unexpected axiom.*Hidden.assumption"):
            build.parse_assumptions(output)

    def test_unicode_axiom_name_is_not_silently_ignored(self):
        output = assumptions_output() + "\u03a9 : Prop\n"
        with self.assertRaisesRegex(RuntimeError, "Unexpected axiom.*\u03a9"):
            build.parse_assumptions(output)

    def test_weaker_or_missing_final_report_is_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "exactly four"):
            build.parse_assumptions(assumptions_output().rsplit("Axioms:", 1)[0])
        output = assumptions_output().rsplit("Axioms:", 1)[0] + "Axioms:\nClassical_Prop.classic : Prop\n"
        with self.assertRaisesRegex(RuntimeError, "assumption sets differ"):
            build.parse_assumptions(output)

    def test_choice_added_to_structural_endpoint_is_rejected(self):
        output = assumptions_output().replace("Classical_Prop.classic", "RelationalChoice.relational_choice", 1)
        with self.assertRaisesRegex(RuntimeError, "assumption sets differ"):
            build.parse_assumptions(output)

    def test_manifest_cannot_authorize_an_additional_axiom(self):
        data = manifest()
        data["allowed_axioms"].append("Hidden.assumption")
        with self.assertRaisesRegex(RuntimeError, "published three"):
            build.validate_manifest(data)


class SourceBoundaryTests(unittest.TestCase):
    def test_valid_source_map(self):
        build.validate_manifest(manifest())

    def test_path_escape_is_rejected_on_both_operating_systems(self):
        for path in ("../outside.v", "/outside.v", "C:/outside.v", "C:\\outside.v", "coq/../outside.v", "coq//Base.v"):
            with self.subTest(path=path):
                data = manifest()
                data["sources"]["PAModel.Base"]["path"] = path
                with self.assertRaises(RuntimeError):
                    build.validate_manifest(data)

    def test_source_cannot_masquerade_as_another_logical_module(self):
        data = manifest()
        data["sources"]["PAModel.Base"]["destination"] = "src/PAModel/PALiteralZFCConsistency.v"
        with self.assertRaisesRegex(RuntimeError, "does not match logical module"):
            build.validate_manifest(data)

    def test_unlisted_dependency_and_reversed_order_are_rejected(self):
        for dependency in ("PAModel.NotPackaged", build.TARGET):
            with self.subTest(dependency=dependency):
                data = manifest()
                data["sources"]["PAModel.Base"]["dependencies"] = [dependency]
                with self.assertRaisesRegex(RuntimeError, "Unpackaged dependency|out of order"):
                    build.validate_manifest(data)

    def test_build_cannot_select_a_different_theorem_target(self):
        data = manifest()
        data["target"] = "PAModel.Base"
        with self.assertRaisesRegex(RuntimeError, "Unexpected classical proof target"):
            build.validate_manifest(data)

    def test_reference_path_cannot_escape_through_a_symbolic_link(self):
        with scratch_directory() as root:
            reference, outside = root / "reference", root / "outside"
            reference.mkdir()
            outside.mkdir()
            try:
                (reference / "escape").symlink_to(outside, target_is_directory=True)
            except OSError:
                self.skipTest("Creating symbolic links is not permitted on this host")
            with self.assertRaisesRegex(RuntimeError, "Path escapes"):
                build.bounded(reference, "escape/source.v")


class KernelTests(unittest.TestCase):
    def setUp(self):
        self.temporary = scratch_directory()
        self.work = self.temporary.__enter__()
        self.patch = patch.object(build, "WORK", self.work)
        self.patch.start()

    def tearDown(self):
        self.patch.stop()
        self.temporary.__exit__(None, None, None)

    def test_checker_recursively_rechecks_the_classical_target(self):
        commands = []

        def run(command, **kwargs):
            commands.append(command)
            # Loaded upstream environments may contain unused axioms. Only the
            # four endpoint Print Assumptions reports determine theorem axioms.
            kwargs["stdout"].write("CONTEXT SUMMARY\n* Axioms: Classical_Prop.classic\n")
            return subprocess.CompletedProcess(command, 0)

        with patch.object(build.subprocess, "check_output", return_value="The Rocq Proof Checker, version 9.1.0"):
            with patch.object(build.subprocess, "run", side_effect=run):
                result = build.check_kernel("coqc", "coqchk", ["-Q", "fresh-src", "PAModel"], {})
        self.assertEqual(result["status"], "PASSED")
        self.assertEqual(commands[0][-1], build.TARGET)
        self.assertNotIn("-admit", commands[0])
        self.assertNotIn("-norec", commands[0])

    def test_checker_failure_overrides_a_misleading_success_sentence(self):
        def run(command, **kwargs):
            kwargs["stdout"].write("Modules were successfully checked\nError: inconsistent assumptions\n")
            return subprocess.CompletedProcess(command, 1)

        with patch.object(build.subprocess, "check_output", return_value="The Rocq Proof Checker, version 9.1.0"):
            with patch.object(build.subprocess, "run", side_effect=run):
                with self.assertRaisesRegex(RuntimeError, "kernel recheck failed"):
                    build.check_kernel("coqc", "coqchk", [], {})
        result = json.loads((self.work / "coqchk-result.json").read_text())
        self.assertEqual(result["status"], "FAILED")
        self.assertEqual(result["exit_code"], 1)


if __name__ == "__main__":
    unittest.main()
