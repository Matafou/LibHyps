#!/bin/bash

DEVOPT=no
STDLIB=

POSITIONAL=()
while [[ $# -gt 0 ]]
do
key="$1"

case $key in
    --stdlib|-stdlib)
        shift
        STDLIB=$1
        shift
        ;;
    --dev)
        DEVOPT=yes
        shift
        ;;
    *)    # unknown option
        POSITIONAL+=("$1") # save it in an array for later
        shift # past argument
        ;;
esac
done

set -- "${POSITIONAL[@]}" # restore positional parameters (i.e.
                          # parameters that were not recognized by the
                          # previous code.)



function gen_projet_file () {
    FILES="$1"
    DIR=$2
    STDLIB=$4
    PROJECTFILE=$DIR/_CoqProject
    RESOURCEFILE=$3

    if [ "$STDLIB" != "" ]
    then
        echo "stdlib detected"
        echo "-Q $STDLIB Stdlib" > "$PROJECTFILE"
    else echo "" > "$PROJECTFILE"
    fi

    cat < $RESOURCEFILE >> "$PROJECTFILE"

    echo "" >> "$PROJECTFILE"

    for i in $FILES
    do
        echo "$i" >> "$PROJECTFILE"
    done

    echo "Content of $PROJECTFILE"

    cat < $PROJECTFILE

    echo "Calling rocq makefile in $DIR"
    (cd $DIR && rocq makefile -f _CoqProject -o Makefile )
}


if [ "$DEVOPT" = "no" ]
then
    FILESLH=$(cd LibHyps && find . -name "*.v" | grep -v "ident_of_string\|especialize_ltac2\|LibEspecialize\|LibHypsDebug" )
else
        FILESLH=$(cd LibHyps && find . -name "*.v" | grep -v "ident_of_string\|especialize_ltac2\|LibEspecialize" )
fi

PROJECTDIRLH="LibHyps"
gen_projet_file "$FILESLH" "$PROJECTDIRLH" "resources/coq_project.libhyps" "$STDLIB"



FILESTEST=$(cd tests && find . -name "*.v" | grep -v "incremental" )
PROJECTDIRTESTS="tests"
gen_projet_file "$FILESTEST" "$PROJECTDIRTESTS" "resources/coq_project.tests" "$STDLIB"
