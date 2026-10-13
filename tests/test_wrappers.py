"""Regression tests for process failures; no Lean installation or API key needed."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from AutoFormalization.proof.evaluate import check
from E3.checker import Checker
from E3.validator import Validator


class WrapperTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        lake = self.root / "lake"
        lake.write_text(f"#!{sys.executable}\n" + """
import json, os, sys, time
print(os.environ.get('FAKE_STDOUT', ''), end='')
print(os.environ.get('FAKE_STDERR', ''), end='', file=sys.stderr)
if os.environ.get('FAKE_SLEEP'):
    time.sleep(30)
if os.environ.get('FAKE_RESULT'):
    with open(sys.argv[-1], 'w') as f:
        json.dump({sys.argv[5]: {'binary_check': 'equiv'}}, f)
sys.exit(int(os.environ.get('FAKE_EXIT', '0')))
""")
        lake.chmod(0o755)
        env = patch.dict(os.environ, {"PATH": str(self.root) + os.pathsep + os.environ["PATH"]})
        env.start()
        self.addCleanup(env.stop)
        self.validator = Validator(str(self.root / "validate"))
        self.checker = Checker(tmp_path=str(self.root / "check"), result_path=str(self.root / "results"))

    def test_validator_accepts_success(self):
        self.assertIsNone(self.validator.validate("True", "valid"))

    def test_validator_rejects_silent_failure(self):
        with patch.dict(os.environ, {"FAKE_EXIT": "1"}):
            self.assertIsNotNone(self.validator.validate("True", "invalid"))

    def test_validator_reports_stderr(self):
        with patch.dict(os.environ, {"FAKE_EXIT": "1", "FAKE_STDERR": "failed to load library"}):
            self.assertIn("failed to load library", self.validator.validate("True", "invalid"))

    def test_checker_accepts_new_result(self):
        with patch.dict(os.environ, {"FAKE_RESULT": "1"}):
            self.assertTrue(self.checker.check("True", "True", "good"))

    def test_checker_missing_result_returns_false(self):
        self.assertFalse(self.checker.check("True", "False", "missing"))

    def test_checker_rejects_stale_result(self):
        output = self.root / "results" / "stale.json"
        output.write_text(json.dumps({"stale": {"binary_check": "equiv"}}))
        with patch.dict(os.environ, {"FAKE_EXIT": "1"}):
            self.assertFalse(self.checker.check("True", "False", "stale"))
        self.assertFalse(output.exists())

    def test_proof_accepts_declarations_without_main(self):
        # The evaluator must typecheck declarations rather than execute main.
        with patch("AutoFormalization.proof.evaluate.run_lean") as run:
            run.return_value = subprocess.CompletedProcess([], 0, b"", b"")
            self.assertTrue(check("proof.lean"))
            self.assertNotIn("--run", run.call_args.args[0])

    def test_proof_rejects_failure_without_error_keyword(self):
        with patch.dict(os.environ, {"FAKE_EXIT": "1", "FAKE_STDERR": "unknown declaration main"}):
            self.assertFalse(check("proof.lean"))

    def test_proof_rejects_sorry(self):
        with patch.dict(os.environ, {"FAKE_STDOUT": "warning: declaration uses 'sorry'"}):
            self.assertFalse(check("proof.lean"))

    def test_timeout_returns_false(self):
        with patch.dict(os.environ, {"FAKE_SLEEP": "1"}):
            self.assertFalse(check("proof.lean", timeout=0.1))

    def test_missing_lake_does_not_crash(self):
        with patch.dict(os.environ, {"PATH": ""}):
            self.assertFalse(check("proof.lean"))
            self.assertFalse(self.checker.check("True", "True", "missing"))
            self.assertIsNotNone(self.validator.validate("True", "missing"))


if __name__ == "__main__":
    unittest.main()
