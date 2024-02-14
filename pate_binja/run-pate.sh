# Shell script used by PATE Binja plugin to run pate.
# This is done with a script so that all is evaluated within the users's shell environment.

if [ "$PATE_BINJA_MODE" = "BUILD" ]
then
    pate="$PATE/pate.sh"
else
    pate="docker run --rm -i -v .:/work --workdir=/work pate"
fi

$pate "$@"

