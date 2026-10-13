#!/bin/bash
# This script was designed to run on GitHub Codespaces.
set -euo pipefail
cd "$(dirname "$0")/.."

# Install elan.
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash -s -- -y
source "$HOME/.elan/env"
# Native SMT plugins load Lake's shared library on Linux.
export LD_LIBRARY_PATH="$(lean --print-prefix)/lib/lean${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

# Build and Install CVC5.
git clone --depth 1 --branch cvc5-1.2.1 https://github.com/cvc5/cvc5 && cd cvc5
./configure.sh production --auto-download
cd build && make -j8 && sudo make install
cd ../..

# Build and Install Z3.
git clone --depth 1 --branch z3-4.13.2 https://github.com/Z3Prover/z3 && cd z3
python3 scripts/mk_make.py
cd build && make -j8 && sudo make install
cd ../..

python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt

# Build the Lean project.
lake script run check
lake exe cache get
lake build SystemE Book UniGeo E3
