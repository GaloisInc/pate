FROM ubuntu:20.04
ENV TZ=America/Los_Angeles
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone
RUN apt update && apt install -y software-properties-common apt-transport-https ca-certificates wget
RUN apt install -y curl zlibc zlib1g zlib1g-dev git zip \
  libgmp3-dev build-essential libtinfo-dev autoconf automake gperf cmake locales \
  python3-distutils python-setuptools antlr3 libantlr3c-dev libtool libtool-bin libboost-all-dev python3-pip \
  libfftw3-dev && \
  locale-gen en_US.UTF-8 && \
  pip3 install toml

RUN apt update && apt install -y zlibc zlib1g libgmp10 libantlr3c-3.4-0 locales && locale-gen en_US.UTF-8

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

RUN mkdir -p /home/yices2/src; \
    git clone https://github.com/SRI-CSL/yices2.git /home/yices2/src && \
    (cd /home/yices2/src; \
     git checkout Yices-2.6.2 && \
     autoconf && \
     ./configure && \
     make -j4 && \
     make install)

RUN mkdir -p /home/z3/src; \
    git clone https://github.com/Z3Prover/z3.git /home/z3/src && \
    cd /home/z3/src && \
    git checkout z3-4.8.10 && \
    mkdir -p /home/z3/bld && \
    (cd /home/z3/bld; \
     cmake -G "Unix Makefiles" -DCMAKE_BUILD_TYPE=Release -DUSE_OPENMP=ON /home/z3/src -DUSE_LIB_GMP=FALSE -DBUILD_LIBZ3_SHARED=OFF /home/z3/src && \
     make -j4 && \
     make install)

RUN mkdir -p /home/cvc4/src; \
    git clone https://github.com/CVC4/CVC4.git /home/cvc4/src && \
    cd /home/cvc4/src && \
    git checkout 1.8 && \
    bash contrib/get-antlr-3.4 && \
    bash contrib/get-cadical && \
    bash contrib/get-kissat && \
    (./configure.sh --cadical --kissat --static --static-binary && \
     cd build && \
     make -j4 && \
     make install)

RUN curl -L https://downloads.haskell.org/~ghcup/0.1.16/x86_64-linux-ghcup-0.1.16 -o /usr/bin/ghcup && chmod +x /usr/bin/ghcup
RUN mkdir -p /root/.ghcup && ghcup --version && ghcup install cabal && ghcup install ghc 8.10.7 && ghcup set ghc 8.10.7

######################################################################
ENV PATH="/root/.ghcup/bin:${PATH}"
RUN cabal update
RUN mkdir -p /home/src

COPY ./cabal.project.dismantle /home/src/cabal.project.dismantle
COPY ./cabal.GHC-8.10.7.freeze /home/src/cabal.freeze
COPY ./submodules/arm-asl-parser /home/src/submodules/arm-asl-parser
COPY ./submodules/asl-translator /home/src/submodules/asl-translator
COPY ./submodules/crucible /home/src/submodules/crucible
COPY ./submodules/dismantle /home/src/submodules/dismantle
COPY ./submodules/dwarf /home/src/submodules/dwarf
COPY ./submodules/elf-edit /home/src/submodules/elf-edit
COPY ./submodules/flexdis86 /home/src/submodules/flexdis86
COPY ./submodules/llvm-pretty /home/src/submodules/llvm-pretty
COPY ./submodules/parameterized-utils /home/src/submodules/parameterized-utils
COPY ./submodules/semmc /home/src/submodules/semmc
COPY ./submodules/what4 /home/src/submodules/what4
COPY ./submodules/what4-serialize /home/src/submodules/what4-serialize

WORKDIR /home/src

RUN cp cabal.project.dismantle cabal.project
RUN cabal v2-configure --keep-going --ghc-options="-fno-safe-haskell"
RUN cabal v2-build --only-dependencies dismantle-arm-xml
RUN cabal v2-build dismantle-arm-xml

COPY ./cabal.project.macaw /home/src/cabal.project.macaw
COPY ./submodules/macaw /home/src/submodules/macaw
COPY ./submodules/macaw-loader /home/src/submodules/macaw-loader

RUN cp cabal.project.macaw cabal.project
RUN cabal v2-build macaw-aarch32 -j1 --ghc-options="+RTS -M5000M"
RUN cabal v2-build semmc-ppc
RUN cabal v2-build lib:semmc-aarch32
RUN cabal v2-build macaw-ppc
RUN cabal v2-build macaw-ppc-symbolic
RUN cabal v2-build macaw-aarch32-symbolic
RUN cabal v2-build macaw-loader-aarch32

COPY ./cabal.project.dist /home/src/cabal.project.dist
COPY ./pate.cabal /home/src/pate.cabal
RUN cp cabal.project.dist cabal.project

RUN cabal v2-build --only-dependencies lib:pate

COPY ./src /home/src/src

COPY ./tools/pate/ /home/src/tools/pate

RUN cabal v2-build lib:pate

COPY ./arch /home/src/arch
COPY ./tools /home/src/tools
COPY ./*.ghci /home/src/

RUN cabal v2-build pate-repl-base

COPY ./pate.sh /home/src/pate.sh

## FROM ubuntu:20.04

ENV PATH="/home/src/:/root/.ghcup/bin:${PATH}"

ENTRYPOINT ["/home/src/pate.sh"]
