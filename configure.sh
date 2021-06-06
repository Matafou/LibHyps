#!/bin/sh

FILES=`find . -name "*.v" -exec echo {} \;`
echo "-R LibHyps LibHyps" > _CoqProject
echo "" >> _CoqProject
for i in `find LibHyps -name "*.v"| grep -v LibHypsNaming2 | grep -v LibHypsExamples | grep -v LibHypsDemo | grep -v LibHypsTest | grep -v LibHypsRegression`; do
  echo $i >> _CoqProject
done
coq_makefile -f _CoqProject -o Makefile
