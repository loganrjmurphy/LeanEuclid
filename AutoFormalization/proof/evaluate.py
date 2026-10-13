import os
import subprocess
import argparse
import tqdm

from E3.process import run_lean
from E3.utils import ROOT_DIR


def check(lean_file, timeout=300):
    try:
        # Proof files contain declarations, not an executable `main`.
        process = run_lean([os.path.abspath(lean_file)], timeout)
        output = (process.stdout + process.stderr).decode(errors="replace")
        return process.returncode == 0 and "declaration uses 'sorry'" not in output
    except (OSError, subprocess.TimeoutExpired):
        return False


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--dataset",
        type=str,
        choices=["Book", "UniGeo"],
        required=True,
        help="Testing dataset",
    )
    parser.add_argument(
        "--category",
        type=str,
        nargs="+",
        choices=[
            "",
            "Parallel",
            "Triangle",
            "Quadrilateral",
            "Congruent",
            "Similarity",
        ],
        required=True,
        help="Testing category",
    )
    parser.add_argument(
        "--reasoning",
        type=str,
        choices=["text-only", "multi-modal"],
        required=True,
        help="Reasoning Type",
    )
    parser.add_argument(
        "--num_examples", type=int, default=0, help="Number of examples"
    )
    args = parser.parse_args()

    tot = 0
    cnt = 0

    for c in args.category:
        print("Category: ", c)
        result_dir = os.path.join(
            ROOT_DIR,
            "result",
            "proof",
            args.dataset,
            args.reasoning,
            str(args.num_examples) + "shot",
            c,
        )

        if args.dataset == "UniGeo":
            testing_idx = range(1, 21)
        else:
            testing_idx = [i for i in range(1, 49) if i not in [2, 6, 12, 32, 42]]

        tot += len(testing_idx)

        for i in tqdm.tqdm(testing_idx):
            result_file = os.path.join(result_dir, str(i) + ".lean")

            if os.path.exists(result_file):
                if check(result_file):
                    cnt += 1

    print(f"cnt: {cnt}, tot: {tot}, acc: {(cnt/tot)*100:.2f}%")


if __name__ == "__main__":
    main()
