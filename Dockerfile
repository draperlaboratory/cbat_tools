FROM binaryanalysisplatform/bap:latest

RUN sudo -E apt install -y zip

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
