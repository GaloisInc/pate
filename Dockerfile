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
ADD https://api.github.com/repos/GaloisInc/pate/git/refs/heads/master version.json
RUN git clone --depth=1 https://github.com/GaloisInc/pate.git /home/src

WORKDIR /home/src
RUN git submodule update --init
RUN cp cabal.project.dist cabal.project
RUN cp cabal.GHC-8.10.7.freeze cabal.project.freeze
RUN cabal v2-configure --ghc-options="-fno-safe-haskell"
RUN cabal v2-build pate-repl-base

## FROM ubuntu:20.04

ENV PATH="/home/src/:/root/.ghcup/bin:${PATH}"

ENTRYPOINT ["/home/src/pate.sh"]
