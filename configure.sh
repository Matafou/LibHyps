#!/bin/bash




function gen_projet_file () {
    FILES="$1"
    PROJECTFILE=$2
    RESOURCEFILE=$3

    cat < $RESOURCEFILE > "$PROJECTFILE"

    echo "" >> "$PROJECTFILE"

    for i in $FILES
    do
        echo "$i" >> "$PROJECTFILE"
    done

    echo "Content of $PROJECTFILE"

    cat < $PROJECTFILE

    echo "Calling coq_makefile in LibHyps"
    (cd LibHyps && coq_makefile -f _CoqProject -o Makefile )
}


FILESLH=$(cd LibHyps && find . -name "*.v" | grep -v "ident_of_string\|especialize_ltac2\|LibEspecialize" )
PROJECTFILELH="LibHyps/_CoqProject"
gen_projet_file "$FILESLH" "$PROJECTFILELH" "resources/coq_project.libhyps"


FILESTEST=$(cd tests && find . -name "*.v" | grep -v "incremental" )
PROJECTFILETESTS="tests/_CoqProject"
gen_projet_file "$FILESTEST" "$PROJECTFILETESTS" "resources/coq_project.tests"
