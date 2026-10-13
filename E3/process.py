"""Run Lean with bounded lifetime and clean up only its own process group."""
import os
import signal
import subprocess

from E3.utils import ROOT_DIR


def run_lean(args, timeout):
    with subprocess.Popen(
        ["lake", "env", "lean", *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=ROOT_DIR,
        start_new_session=True,
    ) as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            # SMT solvers are descendants of this Lean process. Never pkill all
            # z3/cvc5 processes: other builds may be using them concurrently.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.communicate()
            raise
        return subprocess.CompletedProcess(process.args, process.returncode, stdout, stderr)
