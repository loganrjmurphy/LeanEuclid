import os
import signal
import subprocess
import argparse
import tqdm

from subprocess import Popen, PIPE
from AutoFormalization.utils import *


def check(lean_file):
    try:
        command = ['lake', 'env', 'lean', '--run', lean_file]
        process = Popen(command, stdout=PIPE, stderr=PIPE, cwd=ROOT_DIR, preexec_fn=os.setsid)
        stdout, stderr = process.communicate(timeout=5)
        if 'error' not in stdout.decode() and 'error' not in stderr.decode():
            return True
        else:
            return False
    except:
        os.killpg(os.getpgid(process.pid), signal.SIGTERM)
        def kill_running_process(process_name):
            result = subprocess.run(['pgrep', process_name], stdout=subprocess.DEVNULL)
            if not result.returncode:
                subprocess.run(['pkill', process_name], stdout=subprocess.DEVNULL)
        kill_running_process('vampire')
        kill_running_process('cvc5')
        kill_running_process('z3')
        
        return False


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dataset', type=str, choices=['Book', 'UniGeo'], required=True, help='Testing dataset')
    parser.add_argument('--category', type=str, nargs='+', choices=['', 'Parallel', 'Triangle', 'Quadrilateral', 'Congruent', 'Similarity'], required=True, help='Testing category')
    parser.add_argument('--reasoning', type=str, choices=['text-only', 'multi-modal'], required=True, help='Reasoning Type')
    parser.add_argument('--num_examples', type=int, default=0, help='Number of examples')
    args = parser.parse_args()

    tot = 0
    cnt = 0

    for c in args.category:
        print('Category: ', c)
        result_dir = os.path.join(ROOT_DIR, "result", "proof", args.dataset, args.reasoning, str(args.num_examples)+"shot", c)

        if args.dataset == 'UniGeo':
            testing_idx = range(1, 21)
        else:
            testing_idx = [i for i in range(1, 49) if i not in [2, 6, 12, 32, 42]]

        tot += len(testing_idx)

        for i in tqdm.tqdm(testing_idx):
            result_file = os.path.join(result_dir, str(i)+'.lean')

            if os.path.exists(result_file):
                if check(result_file):
                    cnt += 1
    
    print(f'cnt: {cnt}, tot: {tot}, acc: {(cnt/tot)*100:.2f}%')


if __name__ == "__main__":
    main()