"""Exercise the experiment loops with a fake API, without making requests."""
from importlib import import_module
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import Mock, patch


class GenerationTests(unittest.TestCase):
    def exercise(self, kind):
        module = import_module(f"AutoFormalization.{kind}.autoformalize")
        original_root = Path(module.ROOT_DIR)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for index in (1, 3):
                for relative in (f"Book/Prop{index:02d}.lean", f"Book/texts/{index}.txt", f"Book/texts_proofs/{index}.txt"):
                    source = original_root / relative
                    if source.exists():
                        target = root / relative
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copyfile(source, target)
            models = [Mock(), Mock()]
            for model in models:
                model.get_response.side_effect = [RuntimeError("simulated API failure"), "<<< trivial >>>"]
            argv = ["autoformalize", "--dataset", "Book", "--category", "", "--reasoning", "text-only", "--num_query", "2", "--model", "test-model"]
            with patch.object(module, "ROOT_DIR", str(root)), patch.object(module, "GPT4", side_effect=models) as factory, patch.object(module.tqdm, "tqdm", return_value=[1, 3]), patch("sys.argv", argv):
                if kind == "statement":
                    with patch.object(module, "Validator") as validator:
                        validator.return_value.validate.return_value = None
                        module.main()
                else:
                    module.main()
                self.assertEqual(factory.call_count, 2)
                for call in factory.call_args_list:
                    self.assertEqual(call.kwargs["model"], "test-model")
                for model in models:
                    self.assertEqual(model.get_response.call_count, 2)
            extension = "lean" if kind == "proof" else "json"
            for index in (1, 3):
                self.assertTrue((root / "result" / kind / "Book" / "text-only" / "0shot" / f"{index}.{extension}").exists())
            if kind == "proof":
                first = models[0].add_message.call_args_list[0].args[1]
                second = models[1].add_message.call_args_list[0].args[1]
                self.assertNotIn("axiom proposition_1 :", first)
                self.assertIn("axiom proposition_1 :", second)
                self.assertNotIn("{PRECEDING_PROPOSITIONS}", second)

    def test_statement_retries_and_model_override(self):
        self.exercise("statement")

    def test_proof_retries_and_per_problem_context(self):
        self.exercise("proof")
