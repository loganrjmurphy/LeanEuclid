import os
import re
import subprocess

from E3.process import run_lean
from E3.utils import ROOT_DIR, format_test_file


class Validator:
    def __init__(self, tmp_path=os.path.join(ROOT_DIR, "tmp", "validate"), timeout=60):
        self.tmp_path = os.path.abspath(tmp_path)
        self.timeout = timeout
        os.makedirs(self.tmp_path, exist_ok=True)

    def validate(self, expression, instanceName):
        tmpFile = os.path.join(self.tmp_path, instanceName + ".lean")
        os.makedirs(os.path.dirname(tmpFile), exist_ok=True)
        with open(tmpFile, "w", encoding="utf-8") as file:
            file.write(format_test_file(expression))
        try:
            process = run_lean(["--run", tmpFile], self.timeout)
        except (OSError, subprocess.TimeoutExpired) as exc:
            return str(exc)
        output = (process.stdout + process.stderr).decode(errors="replace").strip()
        if process.returncode != 0:
            return output or f"Lean exited with status {process.returncode}"
        if output:
            return re.sub(r"/[^:]+:\d+:\d+: ", "", output)
        return None
