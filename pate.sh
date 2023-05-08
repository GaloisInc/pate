#!/bin/bash

CUR_DIR=$(pwd)
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

temp_ghci_cd=$(mktemp)
temp_ghci=$(mktemp)
echo ":cd ${CUR_DIR}" > ${temp_ghci_cd}
echo ":run \"$@\"" > ${temp_ghci}
echo ":cmd checkAlive" >> ${temp_ghci}
echo "import Pate.Monad" >> ${temp_ghci}
echo "import qualified What4.ExprHelpers as WEH" >> ${temp_ghci}
echo "import qualified What4.Interface as W4" >> ${temp_ghci}
echo "import qualified What4.Expr.Builder as W4B" >> ${temp_ghci}
echo "import qualified Pate.Verification.StrongestPosts as PVS" >> ${temp_ghci}
echo "import qualified Pate.Equivalence.Condition as PEC" >> ${temp_ghci}
echo "import qualified Pate.PatchPair as PPa" >> ${temp_ghci}
echo "import qualified Pate.Verification.Simplify as PSi" >> ${temp_ghci}
echo "import Pate.Verification.PairGraph" >> ${temp_ghci}
echo "import Pate.Verification.PairGraph.Node" >> ${temp_ghci}
echo "import Pate.Verification.AbstractDomain as PAD" >> ${temp_ghci}
cd ${SCRIPT_DIR}
cabal v2-build pate-repl-base && cabal v2-exec ghci -- -v0 -fobject-code -fno-warn-type-defaults -fno-warn-missing-home-modules -threaded -rtsopts "-with-rtsopts=-N -A16M -c" -i"${SCRIPT_DIR}/tools/pate-repl/" -ghci-script ${temp_ghci_cd} -ghci-script "${SCRIPT_DIR}/loadrepl.ghci" -ghci-script ${temp_ghci}
rm ${temp_ghci_cd}
rm ${temp_ghci}


