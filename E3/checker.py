import os
import subprocess
import json

from E3.utils import ROOT_DIR, format_lean_checker_file
from E3.process import run_lean


class Checker:
    def __init__(
        self,
        nperms=3,
        binTime=15,
        approxTime=5,
        mode="skipApprox",
        tmp_path=os.path.join(ROOT_DIR, "tmp", "check"),
        result_path=os.path.join(ROOT_DIR, "results"),
        timeout=600,
    ):
        self.tmp_path = os.path.abspath(tmp_path)
        self.timeout = timeout
        os.makedirs(self.tmp_path, exist_ok=True)
        self.result_path = os.path.abspath(result_path)
        os.makedirs(self.result_path, exist_ok=True)

        self.nPermutations = nperms
        self.equivSolverTime = binTime
        self.approxSolverTime = approxTime
        self.mode = mode

    def check(self, ground, test, instanceName):
        tmpFile = os.path.join(self.tmp_path, instanceName + ".lean")
        os.makedirs(os.path.dirname(tmpFile), exist_ok=True)
        with open(tmpFile, "w", encoding="utf-8") as file:
            leanFile = format_lean_checker_file(ground, test)
            file.write(leanFile)
        outputJsonFile = os.path.join(self.result_path, instanceName + ".json")
        os.makedirs(os.path.dirname(outputJsonFile), exist_ok=True)
        # A failed re-check must never reuse a previous successful result.
        if os.path.exists(outputJsonFile):
            os.remove(outputJsonFile)
        command = [
            "--run",
            tmpFile,
            instanceName,
            self.mode,
            str(self.nPermutations),
            str(self.equivSolverTime),
            str(self.approxSolverTime),
            "true",
            outputJsonFile,
        ]
        try:
            process = run_lean(command, self.timeout)
            if process.returncode != 0:
                return False
            with open(outputJsonFile, "r", encoding="utf-8") as f:
                data = json.load(f)
            return data[instanceName].get("binary_check") == "equiv"
        except (OSError, ValueError, KeyError, TypeError, subprocess.TimeoutExpired):
            return False
