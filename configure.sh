#!/bin/bash




function gen_projet_file () {
    FILES="$1"
    DIR=$2
    PROJECTFILE=$DIR/_CoqProject
    RESOURCEFILE=$3

    cat < $RESOURCEFILE > "$PROJECTFILE"

    echo "" >> "$PROJECTFILE"

    for i in $FILES
    do
        echo "$i" >> "$PROJECTFILE"
    done

    echo "Content of $PROJECTFILE"

    cat < $PROJECTFILE

    echo "Calling coq_makefile in $DIR"
    (cd $DIR && coq_makefile -f _CoqProject -o Makefile )
}


FILESLH=$(cd LibHyps && find . -name "*.v" | grep -v "ident_of_string\|especialize_ltac2\|LibEspecialize" )
PROJECTDIRLH="LibHyps"
gen_projet_file "$FILESLH" "$PROJECTDIRLH" "resources/coq_project.libhyps"


FILESTEST=$(cd tests && find . -name "*.v" | grep -v "incremental" )
PROJECTDIRTESTS="tests"
gen_projet_file "$FILESTEST" "$PROJECTDIRTESTS" "resources/coq_project.tests"
