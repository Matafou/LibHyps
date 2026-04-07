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
    echo "LibHypsDebug.v shoiuld not be compiled in a released code."
    echo "Use ./configure.sh to remove rerferences to debug code."
    echo "then make clean; make lib tests"
    echo "If this fails, remove the calls to LibHypsDebug.v in the code"
    exit 1
else
    exit 0
fi
