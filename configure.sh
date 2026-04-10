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
    -dev|--dev)
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

    command -v rocq ; rocqexists=$?
    if [ $rocqexists -eq 0 ]
    then
       echo "Calling rocq makefile in $DIR"
       (cd $DIR && rocq makefile -f _CoqProject -o Makefile )
    else
        command -v coqc ; coqexists=$?
        if [ $coqexists -eq 0 ]
         then
             echo "Calling coq_makefile in $DIR"
             (cd $DIR && coq_makefile -f _CoqProject -o Makefile )
         else
             echo "Neither rocq nor coq executable found"
             exit 1
        fi
    fi
}


if [ "$DEVOPT" = "no" ]
then
    FILESLH=$(cd LibHyps && find . -name "*.v" | grep -v "LibHypsDebug" )
else
    FILESLH=$(cd LibHyps && find . -name "*.v"  )
fi

PROJECTDIRLH="LibHyps"
gen_projet_file "$FILESLH" "$PROJECTDIRLH" "resources/coq_project.libhyps" "$STDLIB"



FILESTEST=$(cd tests && find . -name "*.v" | grep -v "incremental" )
PROJECTDIRTESTS="tests"
gen_projet_file "$FILESTEST" "$PROJECTDIRTESTS" "resources/coq_project.tests" "$STDLIB"
