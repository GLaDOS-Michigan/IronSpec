#!/bin/bash

cd /proj/vm-vm-PG0/BASE-DIRECTORY/dafny-holeEval
for i in $@;
do
    workingDir=/mnt/output_new_holeEval_agents.dfy_${i};
    rm -rf ${workingDir};
    mkdir -p ${workingDir};
    ./Binaries/Dafny /rlimit:100000 /compile:0 /allowGlobals /noNLarith /autoTriggers:1 /verifyAllModules /holeEvalWorkingDir:${workingDir} /holeEvalRunOnce /holeEvalBase:Synod.PaxosNextOneAgent /holeEvalRemoveFileLine:agents.dfy:${i} /holeEvalCons:"Proof_Agreement_Invs.Agreement_Chosen_Inv(PaxosNextOneAgent_c, PaxosNextOneAgent_s) && Proof_Agreement_Invs.Agreement_Chosen_Inv(PaxosNextOneAgent_c, PaxosNextOneAgent_s')" /proj/vm-vm-PG0/BASE-DIRECTORY/paxos_proof/paxos/proof_agreement.dfy &> ${workingDir}/output.txt;
done