#!/bin/bash


## Explanation
# - Debug code is in LibHyps/LibHypsDebug.v
#
# - by default ./configure.sh does ignores this file
# - unless we use ./configure.sh --dev
#
# - the present test checks that we have not forgotten to remove
# - refrences to the debug file (by doing ./configure.sh).
#
echo "Sanity check (debug files)"
if grep -q "LibHypsDebug.v"  LibHyps/_CoqProject
then
    echo "REMAINING DEBUG CODE: ABORTING."
    echo "Use ./configure.sh to remove rerferences to debug code."
    echo "then make clean; make lib tests"
    exit 1
else
    exit 0
fi
