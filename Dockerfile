FROM ubuntu:latest

WORKDIR /LeanEuclid
COPY . .

# Install dependencies.
RUN apt-get update && apt-get install -y curl git cmake python3-venv python3-pip

# Build and Install CVC5.
RUN git clone https://github.com/cvc5/cvc5
WORKDIR cvc5
RUN ./configure.sh --auto-download
WORKDIR build
RUN make -j$(nproc)
RUN sudo make install
WORKDIR /LeanEuclid

# Build and Install Z3.
RUN git clone https://github.com/Z3Prover/z3
WORKDIR z3
RUN python3 scripts/mk_make.py
WORKDIR build
RUN make -j$(nproc)
RUN sudo make install
WORKDIR /LeanEuclid

# Install smt-portfolio.
RUN pip3 install --upgrade pip
RUN pip3 install smt-portfolio

# Install elan.
ENV ELAN_HOME="/.elan"
ENV PATH="${ELAN_HOME}/bin:${PATH}"
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash -s -- -y

# Build the Lean project.
RUN lake script run check
RUN lake exe cache get
RUN lake build SystemE Book UniGeo E3
RUN lake -R -Kenv=dev build SystemE:docs
