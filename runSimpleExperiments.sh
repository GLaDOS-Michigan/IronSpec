#!/bin/bash

./cleanExperimentOutput.sh


echo -e "Starting Mutation Testing for Max Spec (Correct)"

mkdir experimentOutput/MaxSpecCorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:maxExample.maxSpec /proofName:maxTest.maxT  /proofLocation:"$(pwd)/specs/max/lemmaMaxTestCorrect.dfy" /serverIpPortList:ipPorts.txt $(pwd)/specs/max/maxSpec.dfy &> experimentOutput/MaxSpecCorrect/maxSpecCorrect_output.txt

mkdir experimentOutput/MaxSpecCorrect/outputLogs
cp ./outputLogs/* experimentOutput/MaxSpecCorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Max Spec (Correct) - output found in ./experimentOutput/MaxSpecCorrect/maxSpecCorrect_output.txt \n"

####

echo -e "Starting Automatic Sanity Checker(ASC) Testing for Sort"

mkdir experimentOutput/sortASC

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:sort.SortSpec /proofName:sort.merge_sort /mutationRootName:sort.SortSpec /proofLocation:"$(pwd)/specs/sort/sortMethod.dfy" /serverIpPortList:ipPorts.txt /checkInputAndOutputSpecified $(pwd)/specs/sort/sortMethod.dfy &> experimentOutput/sortASC/sortASC_output.txt

echo -e "DONE ASC Testing for sort - output found in ./experimentOutput/sortASC/sortASC_output.txt \n"
