"""Regression cases for incomplete audits and failed source scans."""

from pathlib import Path
from contextlib import redirect_stdout, redirect_stderr
from io import StringIO
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from scripts import check_axioms, check_proofs


class AxiomAuditTests(unittest.TestCase):
    def setUp(self):
        self.names = sorted(check_axioms.EXPECTED)
        self.commands = "\n".join(f"#print axioms {n}" for n in self.names)
        self.reports = "\n".join(
            f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            for n in self.names
        )

    def test_complete_audit(self):
        check_axioms.check_commands(self.commands)
        check_axioms.check_reports(self.reports)

    def test_empty_inventory_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "missing theorems"):
            check_axioms.check_commands("import EAB\n")

    def test_missing_endpoint_is_rejected(self):
        source = self.commands.replace(
            "#print axioms EAB.Paper.Chain.stopped_forest_law", ""
        )
        with self.assertRaisesRegex(ValueError, "stopped_forest_law"):
            check_axioms.check_commands(source)

    def test_duplicate_command_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "duplicate theorems"):
            check_axioms.check_commands(
                self.commands + f"\n#print axioms {self.names[0]}"
            )

    def test_same_count_with_wrong_name_is_rejected(self):
        text = self.reports.replace(self.names[0], "EAB.Paper.wrong_theorem")
        with self.assertRaisesRegex(ValueError, "unexpected theorems"):
            check_axioms.check_reports(text)

    def test_duplicate_report_is_rejected(self):
        text = self.reports.replace(self.names[0], self.names[1])
        with self.assertRaisesRegex(ValueError, "duplicate theorems"):
            check_axioms.check_reports(text)

    def test_truncated_report_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "missing theorems"):
            check_axioms.check_reports(self.reports.rsplit("\n", 1)[0])

    def test_unexpected_axioms_are_rejected(self):
        for axiom in ["sorryAx", "Lean.ofReduceBool", "Project.assumption"]:
            with self.subTest(axiom=axiom):
                text = self.reports.replace("propext", axiom, 1)
                with self.assertRaisesRegex(ValueError, "unexpected axioms"):
                    check_axioms.check_reports(text)

    def test_axiom_free_report_is_accepted(self):
        first = self.reports.splitlines()[0]
        text = self.reports.replace(
            first, f"'{self.names[0]}' does not depend on any axioms"
        )
        check_axioms.check_reports(text)

    def test_lean_compile_failure_is_rejected(self):
        output = subprocess.CompletedProcess([], 1, self.reports, "Lean failed")
        with patch.object(check_axioms.subprocess, "run", return_value=output), \
                redirect_stdout(StringIO()), redirect_stderr(StringIO()):
            self.assertEqual(check_axioms.main(), 1)


class ProofScanTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "EAB/Paper").mkdir(parents=True)
        for name in ["EAB.lean", "AxiomCheck.lean", "EAB/Paper/Example.lean"]:
            (self.root / name).write_text("-- source\n", encoding="utf-8")

    def test_complete_source_scan(self):
        self.assertEqual(check_proofs.check_sources(self.root), 3)

    def test_markers_in_modules_and_root_files_are_rejected(self):
        for name, marker in [("EAB/Paper/Example.lean", "sorry"),
                             ("EAB.lean", "admit"),
                             ("AxiomCheck.lean", "sorry")]:
            with self.subTest(name=name):
                path = self.root / name
                path.write_text(marker + "\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "unfinished proof"):
                    check_proofs.check_sources(self.root)
                path.write_text("-- source\n", encoding="utf-8")

    def test_missing_source_directory_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "directory EAB is missing"):
            check_proofs.check_sources(self.root / "absent")

    def test_empty_module_inventory_is_rejected(self):
        (self.root / "EAB/Paper/Example.lean").unlink()
        with self.assertRaisesRegex(ValueError, "no Lean modules"):
            check_proofs.check_sources(self.root)

    def test_missing_root_file_is_rejected(self):
        (self.root / "AxiomCheck.lean").unlink()
        with self.assertRaises(OSError):
            check_proofs.check_sources(self.root)

    def test_unreadable_file_is_rejected(self):
        with patch.object(Path, "read_text", side_effect=PermissionError("denied")):
            with self.assertRaises(PermissionError):
                check_proofs.check_sources(self.root)

    def test_directory_scan_error_is_rejected(self):
        def failed_walk(*args, **kwargs):
            kwargs["onerror"](PermissionError("directory denied"))

        with patch.object(check_proofs.os, "walk", side_effect=failed_walk):
            with self.assertRaises(PermissionError):
                check_proofs.check_sources(self.root)

    def test_invalid_utf8_is_rejected(self):
        (self.root / "EAB/Paper/Example.lean").write_bytes(b"\xff")
        with self.assertRaises(UnicodeError):
            check_proofs.check_sources(self.root)


if __name__ == "__main__":
    unittest.main()
