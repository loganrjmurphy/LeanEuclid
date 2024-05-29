#!/bin/bash

# Install elan.
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash -s -- -y
source $HOME/.elan/env

# Build and Install CVC5.
git clone https://github.com/cvc5/cvc5 && cd cvc5
./configure.sh --auto-download
cd build && make -j8 && sudo make install
cd ../..

# Build and Install Z3.
git clone https://github.com/Z3Prover/z3 && cd z3
python3 scripts/mk_make.py
cd build && make -j8 && sudo make install
cd ../..

pip install smt-portfolio

lake script run check
lake exe cache get
lake build SystemE Book UniGeo E3