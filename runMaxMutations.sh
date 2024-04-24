#!/bin/bash

./cleanExperimentOutput.sh


echo -e "Starting Mutation Testing for Max Spec (Correct)"

mkdir experimentOutput/MaxSpecCorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:maxExample.maxSpec /proofName:maxTest.maxT   /proofLocation:"$(pwd)/specs/max/lemmaMaxTestCorrect.dfy" /serverIpPortList:ipPorts.txt $(pwd)/specs/max/maxSpec.dfy &> experimentOutput/MaxSpecCorrect/maxSpecCorrect_output.txt

mkdir experimentOutput/MaxSpecCorrect/outputLogs
cp ./outputLogs/* experimentOutput/MaxSpecCorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Max Spec (Correct) - output found in ./experimentOutput/MaxSpecCorrect/maxSpecCorrect_output.txt \n"
