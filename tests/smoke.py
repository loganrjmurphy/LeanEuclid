"""Offline integration checks. Run after `lake build SystemE Book UniGeo E3`."""
import json
from pathlib import Path
import tempfile

from AutoFormalization.proof.evaluate import check
from E3.checker import Checker
from E3.validator import Validator
from E3.process import run_lean
from E3.utils import ROOT_DIR


def main():
    with tempfile.TemporaryDirectory(prefix="leaneuclid-smoke-") as directory:
        root = Path(directory)
        # Prompt theorem lists must agree with the declarations the model can use.
        declarations = json.loads((Path(ROOT_DIR) / "AutoFormalization" / "proof" / "book_propositions.json").read_text())
        source = "import Book\nset_option autoImplicit false\n"
        for entries in declarations.values():
            for declaration in entries:
                name, signature = declaration.split(" : ", 1)
                source += f"example : {signature} := Elements.Book1.{name}\n"
        signatures = root / "signatures.lean"
        signatures.write_text(source)
        process = run_lean([str(signatures)], 120)
        assert process.returncode == 0, (process.stdout + process.stderr).decode(errors="replace")
        process = run_lean(["--run", str(Path(ROOT_DIR) / "tests" / "E3Regression.lean"), str(root / "nested" / "output.json")], 120)
        assert process.returncode == 0, (process.stdout + process.stderr).decode(errors="replace")
        validator = Validator(str(root / "validate"))
        statement = "∀ (a b : Point), a ≠ b → b ≠ a"
        assert validator.validate(statement, "valid") is None
        assert validator.validate("not_a_Lean_expression", "invalid") is not None
        checker = Checker(tmp_path=str(root / "check"), result_path=str(root / "result"))
        assert checker.check(statement, statement, "identity")
        assert not checker.check(statement, "not_a_Lean_expression", "identity")
        for name, proof, expected in [("valid", "trivial", True), ("invalid", "exact False.intro", False), ("incomplete", "sorry", False)]:
            path = root / f"{name}.lean"
            path.write_text(f"theorem smoke : True := by {proof}\n")
            assert check(str(path)) is expected, name
        checker.mode = "onlyApprox"
        checker.check(statement, statement, "approx")
        result = json.loads((root / "result" / "approx.json").read_text())["approx"]
        approx = result["approx_check"]
        assert isinstance(approx, list) and approx, result
        assert any(
            all(permutation[direction]["solved"] == permutation[direction]["total"]
                for direction in ("fwdLHS", "bwdLHS", "fwdRHS", "bwdRHS"))
            for entry in approx for permutation in entry.values()
        ), result
    print("Smoke checks passed: Lean validation, proof evaluation, E3 standard and approximate equivalence.")


if __name__ == "__main__":
    main()
