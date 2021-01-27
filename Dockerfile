FROM binaryanalysisplatform/bap:latest

RUN git clone https://github.com/draperlaboratory/cbat_tools.git

RUN cd cbat_tools/wp; \
    opam config exec -- make

RUN cd cbat_tools/bildb; \
    opam config exec -- make

WORKDIR /home/opam/cbat_tools
