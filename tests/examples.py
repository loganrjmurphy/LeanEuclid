"""Typecheck the few-shot examples that are outside the Lake library targets."""
import argparse
from pathlib import Path

from AutoFormalization.proof.evaluate import check
from E3.utils import ROOT_DIR


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", choices=["Book", "UniGeo"])
    args = parser.parse_args()
    root = Path(ROOT_DIR)
    example_dir = root / "AutoFormalization" / "example"
    if args.dataset:
        example_dir /= args.dataset
    files = sorted(example_dir.rglob("*.lean"))
    failed = []
    for path in files:
        passed = check(str(path))
        print(f"{'PASS' if passed else 'FAIL'} {path.relative_to(root)}", flush=True)
        if not passed:
            failed.append(path)
    if failed:
        raise SystemExit(f"{len(failed)} of {len(files)} example files failed")
    print(f"All {len(files)} example files passed.")


if __name__ == "__main__":
    main()
