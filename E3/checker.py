import os
import signal
import json

from E3.utils import *
from subprocess import Popen, PIPE


class Checker:
    def __init__(
        self,
        nperms=3,
        binTime=15,
        approxTime=5,
        mode="skipApprox",
        tmp_path=os.path.join(ROOT_DIR, "tmp", "check"),
        result_path=os.path.join(ROOT_DIR, "results"),
    ):
        self.tmp_path = tmp_path
        os.makedirs(self.tmp_path, exist_ok=True)
        self.result_path = result_path
        os.makedirs(self.result_path, exist_ok=True)

        self.nPermutations = nperms
        self.equivSolverTime = binTime
        self.approxSolverTime = approxTime
        self.mode = mode

    def check(self, ground, test, instanceName):
        tmpFile = os.path.join(self.tmp_path, instanceName + ".lean")
        with open(tmpFile, "w") as file:
            leanFile = format_lean_checker_file(ground, test)
            file.write(leanFile)
        outputJsonFile = os.path.join(self.result_path, instanceName + ".json")
        command = [
            "lake",
            "env",
            "lean",
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
        process = Popen(
            command, stdin=PIPE, stdout=PIPE, cwd=ROOT_DIR, preexec_fn=os.setsid
        )
        try:
            process.communicate()
            with open(outputJsonFile, "r", encoding="utf-8") as f:
                data = json.load(f)

            result = data[instanceName]["binary_check"]
            if result == "equiv":
                return True
            else:
                return False
        except:
            os.killpg(os.getpgid(process.pid), signal.SIGTERM)
            return False
