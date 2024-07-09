## Clone git into image
FROM --platform=linux/amd64 ubuntu:20.04 as gitbase

RUN apt update && apt install -y ssh
RUN apt install -y git

RUN mkdir /home/src-git
COPY ./.git /home/src-git/.git

WORKDIR /home/src-git
RUN git rev-parse HEAD > /tmp/git-rev
RUN git clone --depth=1 /home/src-git /home/src
WORKDIR /home/src
RUN git checkout $(cat /tmp/git-rev)

RUN git config --global protocol.file.allow always

RUN sed -i "s/url = https:\/\/github.com\/.*\/\(.*\)\.git/url = \/home\/src-git\/.git\/modules\/submodules\/\1/g" .gitmodules
RUN sed -i "s/url = git@github.com:.*\/\(.*\)\.git/url = \/home\/src-git\/.git\/modules\/submodules\/\1/g" .gitmodules

RUN mv /home/src-git/.git/modules/tools/pate/static/* /home/src-git/.git/modules/submodules/
# RUN git config --global url."https://github.com/".insteadOf "git@github.com:"
RUN git submodule update --init

# delete all git files, since we don't want to copy them
RUN find submodules -name .git -exec rm -rf {} \;
RUN rm -r .git
RUN find . -name .gitmodules -exec rm {} \;
RUN find . -name .gitignore -exec rm {} \;


## Build project in image
FROM --platform=linux/amd64 ubuntu:20.04
ENV GHC_VERSION=9.6.2
ENV TZ=America/Los_Angeles
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone
RUN apt update && \
    apt install -y software-properties-common curl zlibc zlib1g zlib1g-dev git libgmp3-dev build-essential # Version 1

RUN add-apt-repository -y ppa:sri-csl/formal-methods
RUN apt-get update
RUN apt-get install -y yices2

RUN curl https://downloads.haskell.org/~ghcup/x86_64-linux-ghcup -o /usr/bin/ghcup && chmod +x /usr/bin/ghcup
RUN mkdir -p /root/.ghcup && ghcup install-cabal
RUN ghcup install ghc ${GHC_VERSION} && ghcup set ghc ${GHC_VERSION} 

RUN apt install locales
RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8


######################################################################
ENV PATH="/root/.ghcup/bin:${PATH}"
RUN cabal v2-update
RUN mkdir -p /home/src
RUN mkdir -p /home/src/submodules

COPY --from=gitbase /home/src/cabal.project.dist /home/src/cabal.GHC-${GHC_VERSION}.freeze  /home/src/
WORKDIR /home/src

RUN cp cabal.GHC-${GHC_VERSION}.freeze cabal.project.freeze
RUN cp cabal.project.dist cabal.project
RUN cabal --version ; ghc --version

RUN sed -i "1s/.*/optional-packages:/" cabal.project

# llvm-pretty
COPY --from=gitbase /home/src/submodules/llvm-pretty /home/src/submodules/llvm-pretty
RUN cabal v2-build llvm-pretty

# parameterized-utils
COPY --from=gitbase /home/src/submodules/parameterized-utils /home/src/submodules/parameterized-utils
RUN cabal v2-build parameterized-utils

# what4
COPY --from=gitbase /home/src/submodules/what4 /home/src/submodules/what4
RUN cabal v2-build what4

# crucible
COPY --from=gitbase /home/src/submodules/crucible /home/src/submodules/crucible
RUN cabal v2-build crucible
 
# arm-asl-parser
COPY --from=gitbase /home/src/submodules/arm-asl-parser /home/src/submodules/arm-asl-parser
RUN cabal v2-build asl-parser

# dismantle
COPY --from=gitbase /home/src/submodules/dismantle /home/src/submodules/dismantle
RUN cabal v2-build dismantle-tablegen dismantle-arm-xml dismantle-ppc

# asl-translator
COPY --from=gitbase /home/src/submodules/asl-translator /home/src/submodules/asl-translator
RUN cabal v2-build asl-translator

# elf-edit
COPY --from=gitbase /home/src/submodules/elf-edit /home/src/submodules/elf-edit
RUN cabal v2-build elf-edit

# semmc
COPY --from=gitbase /home/src/submodules/semmc /home/src/submodules/semmc
RUN cabal v2-build semmc semmc-aarch32 semmc-ppc semmc-synthesis semmc-learning

# galois-dwarf
COPY --from=gitbase /home/src/submodules/dwarf /home/src/submodules/dwarf
RUN cabal v2-build galois-dwarf

# flexdis86
COPY --from=gitbase /home/src/submodules/flexdis86 /home/src/submodules/flexdis86
RUN cabal v2-build binary-symbols flexdis86

#mutual dependency between these submodules
# macaw
COPY --from=gitbase /home/src/submodules/macaw /home/src/submodules/macaw
 
# macaw-loader
COPY --from=gitbase /home/src/submodules/macaw-loader /home/src/submodules/macaw-loader
RUN cabal v2-build macaw-base macaw-loader macaw-semmc

RUN cabal v2-build macaw-ppc macaw-loader-ppc
RUN cabal v2-build macaw-x86 macaw-loader-x86
RUN cabal v2-build macaw-aarch32 macaw-loader-aarch32

# demangler
COPY --from=gitbase /home/src/submodules/demangler /home/src/submodules/demangler
RUN cabal v2-build demangler

# This step is a catch-all that builds the rest of the project
# dependencies.
# Notably these submodules may be stale in the cache, but
# the next step ensures everything is brought up to date.
COPY --from=gitbase /home/src/pate.cabal /home/src/pate.cabal

RUN cp cabal.project.dist cabal.project
RUN cabal v2-build pkg:pate --only-dependencies

COPY --from=gitbase /home/src/src /home/src/src
COPY --from=gitbase /home/src/arch /home/src/arch
COPY --from=gitbase /home/src/tools /home/src/tools
COPY --from=gitbase /home/src/tests /home/src/tests
COPY --from=gitbase /home/src/pate.sh /home/src/pate.sh

RUN cabal v2-build pate-repl-base

ENV PATH="/home/src/:/root/.ghcup/bin:${PATH}"

COPY --from=gitbase /home/src/loadrepl.ghci /home/src/loadrepl.ghci
RUN apt install -y libtinfo5 libtinfo-dev expect-lite
ENTRYPOINT ["/home/src/pate.sh"]


