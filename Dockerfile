FROM ocaml/opam:ubuntu-20.04-ocaml-4.14

RUN sudo -E apt update; \
    sudo -E apt install -qq -yy \
    zip binutils-multiarch clang debianutils libgmp-dev \
    libncurses5-dev libzip-dev llvm-10-dev pkg-config zlib1g-dev

RUN opam repo add opam https://opam.ocaml.org/; \
    opam install core z3; \
    opam repo add bap-testing \
    git+https://github.com/BinaryAnalysisPlatform/opam-repository#testing; \
    opam depext --install -y bap

RUN git clone https://github.com/BinaryAnalysisPlatform/bap-toolkit.git

RUN cd bap-toolkit; \
    opam config exec -- make; \
    opam config exec -- make install

RUN git clone https://github.com/draperlaboratory/cbat_tools.git

RUN cd cbat_tools/wp; \
    opam config exec -- make

RUN cd cbat_tools/bildb; \
    opam config exec -- make

WORKDIR /home/opam/cbat_tools
