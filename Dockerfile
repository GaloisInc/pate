FROM --platform=linux/amd64 ubuntu:20.04
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

# Ensure that submodule remotes use https instead of ssh so we can pull
# them without setting up ssh credentials
RUN git config --global url."https://github.com/".insteadOf "git@github.com:"
RUN git config --global url."https://".insteadOf "git://"
# Get a fresh repo clone to avoid local changes
# This ADD is to ensure the cache updates if this repo changes

RUN git clone --depth=1 https://github.com/GaloisInc/pate.git /home/src

WORKDIR /home/src

RUN cp cabal.project.dist cabal.project
RUN cp cabal.GHC-8.10.7.freeze cabal.project.freeze
RUN sed -i "1s/.*/optional-packages:/" cabal.project
RUN cabal v2-configure --ghc-options="-fno-safe-haskell"

# The pattern below allows us to incrementally build the submodules
# for this project, where each individual step only depends on the
# specific revision on the master branch for pate.
# In particular, this allows us to cache the builds for the
# revisions of these submodules.

# We don't need to cache all submodule builds, this step is
# optional and intended to avoid re-building large packages
# (e.g. macaw-aarch32). After these cached steps, the full set
# of submodules is checked out in order to finish the build.

# Notably, these cached steps can be safely deleted as they are purely
# an optimization.

# parameterized-utils
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/parameterized-utils parameterized-utils.json
RUN git submodule update --init -- submodules/parameterized-utils
RUN cabal v2-build parameterized-utils

# what4
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/what4 what4.json
RUN git submodule update --init -- submodules/what4
RUN cabal v2-build what4

# llvm-pretty
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/llvm-pretty llvm-pretty.json
RUN git submodule update --init -- submodules/llvm-pretty
RUN cabal v2-build llvm-pretty

# crucible
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/crucible crucible.json
RUN git submodule update --init -- submodules/crucible
RUN cabal v2-build crucible

# what4-serialize
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/what4-serialize what4-serialize.json
RUN git submodule update --init -- submodules/what4-serialize
RUN cabal v2-build what4-serialize

# arm-asl-parser
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/arm-asl-parser arm-asl-parser.json
RUN git submodule update --init -- submodules/arm-asl-parser
RUN cabal v2-build asl-parser

# dismantle
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/dismantle dismantle.json
RUN git submodule update --init -- submodules/dismantle
RUN cabal v2-build dismantle-tablegen dismantle-arm-xml dismantle-ppc

# asl-translator
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/asl-translator asl-translator.json
RUN git submodule update --init -- submodules/asl-translator
RUN cabal v2-build asl-translator

# elf-edit
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/elf-edit elf-edit.json
RUN git submodule update --init -- submodules/elf-edit
RUN cabal v2-build elf-edit

# semmc
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/semmc semmc.json
RUN git submodule update --init -- submodules/semmc
RUN cabal v2-build semmc semmc-aarch32 semmc-ppc

# dwarf
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/dwarf dwarf.json
RUN git submodule update --init -- submodules/dwarf
RUN cabal v2-build galois-dwarf

# flexdis86
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/flexdis86 flexdis86.json
RUN git submodule update --init -- submodules/flexdis86
RUN cabal v2-build binary-symbols

#mutual dependency between these submodules
# macaw
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/macaw macaw.json
RUN git submodule update --init -- submodules/macaw

# macaw-loader
ADD https://api.github.com/repos/GaloisInc/pate/contents/submodules/macaw-loader macaw-loader.json
RUN git submodule update --init -- submodules/macaw-loader
RUN cabal v2-build macaw-base macaw-loader 

RUN cabal v2-build macaw-ppc macaw-loader-ppc
RUN cabal v2-build macaw-aarch32 macaw-loader-aarch32

# After the cached submodule steps, we now add the dependency on the current pate revision, so
# any changes to non-cached submodules (or pate itself) are captured.
ADD https://api.github.com/repos/GaloisInc/pate/git/refs/heads/master version.json
# Notably our previous 'git clone' was not guarded with the above, and so the
# cache may be stale. We run 'git pull' to ensure the repository is up to date.
RUN git pull
RUN git submodule update --init
RUN cp cabal.project.dist cabal.project
RUN cabal v2-build pate-repl-base

FROM --platform=linux/amd64 ubuntu:20.04

RUN apt update && apt install -y build-essential libgmp3-dev libtinfo-dev zlib1g-dev zlibc zlib1g libgmp10 libantlr3c-3.4-0 locales && locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

COPY --from=0 /usr/local/bin/cvc4 \
              /usr/local/bin/z3 \
              /usr/local/bin/yices \
              /usr/local/bin/yices-smt2 \
              /usr/local/bin/

COPY --from=0 /root/.ghcup /root/.ghcup
COPY --from=0 /root/.cabal /root/.cabal
COPY --from=0 /home/src /home/src

ENV PATH="/home/src/:/root/.ghcup/bin:${PATH}"

ENTRYPOINT ["/home/src/pate.sh"]
