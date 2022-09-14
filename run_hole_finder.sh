#!/bin/bash

cd /proj/vm-vm-PG0/BASE-DIRECTORY/dafny-holeEval
for i in $@;
do
    rm -rf output_callGraph_agents.dfy_${i};
    mkdir -p output_callGraph_agents.dfy_${i};
    rm -rf /tmp/*holeFinder_*
    ./Binaries/Dafny /rlimit:100000 /compile:0 /allowGlobals /noNLarith /autoTriggers:1 /verifyAllModules /holeFinder:Synod.Next /holeEvalRemoveFileLine:agents.dfy:${i} /holeEvalCons:"Proof_Agreement_Invs.Agreement_Chosen_Inv(Next_c, Next_s) && Proof_Agreement_Invs.Agreement_Chosen_Inv(Next_c, Next_s')" /proj/vm-vm-PG0/BASE-DIRECTORY/paxos_proof/paxos/proof_agreement.dfy &> output_callGraph_agents.dfy_${i}/output.txt;
    mv /tmp/*holeFinder_* output_callGraph_agents.dfy_${i}/;
done