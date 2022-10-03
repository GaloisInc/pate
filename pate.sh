#!/bin/bash
temp_ghci=$(mktemp)
echo ":run \"$@\"" > ${temp_ghci}
echo ":cmd checkAlive" >> ${temp_ghci}
cabal v2-build pate-repl-base
cabal v2-exec ghci -- -fobject-code -fno-warn-type-defaults -fno-warn-missing-home-modules -threaded -rtsopts "-with-rtsopts=-N -A16M -c" -v0 -i./tools/pate-repl/ -ghci-script loadrepl.ghci -ghci-script ${temp_ghci}
rm ${temp_ghci}


