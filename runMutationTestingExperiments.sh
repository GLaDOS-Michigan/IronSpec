#!/bin/bash

echo -e "Running IronSpec MutationTesting Experiments \n"

# # --------------

echo -e "Starting Mutation Testing for Max Spec (Correct)"

mkdir experimentOutput/MaxSpecCorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:maxExample.maxSpec /proofName:maxTest.maxT   /proofLocation:"$(pwd)/specs/max/lemmaMaxTestCorrect.dfy" /serverIpPortList:ipPorts.txt $(pwd)/specs/max/maxSpec.dfy &> experimentOutput/MaxSpecCorrect/maxSpecCorrect_output.txt

mkdir experimentOutput/MaxSpecCorrect/outputLogs
cp ./outputLogs/* experimentOutput/MaxSpecCorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Max Spec (Correct) - output found in ./experimentOutput/MaxSpecCorrect/maxSpecCorrect_output.txt \n"

# --------------


echo -e "Starting Mutation Testing for Max Spec (Incorrect)"

mkdir experimentOutput/MaxSpecIncorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:maxExample.maxSpec /proofName:maxTest.maxT   /proofLocation:"$(pwd)/specs/max/lemmaMaxTest.dfy" /serverIpPortList:ipPorts.txt $(pwd)/specs/max/maxSpec.dfy &> experimentOutput/MaxSpecIncorrect/maxSpecIncorrect_output.txt

mkdir experimentOutput/MaxSpecIncorrect/outputLogs
cp ./outputLogs/* experimentOutput/MaxSpecIncorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Max Spec (Incorrect) - output found in ./experimentOutput/MaxSpecIncorrect/maxSpecIncorrect_output.txt \n"

# --------------

echo -e "Starting Mutation Testing for Sort Spec (Correct)"

mkdir experimentOutput/SortSpecCorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:sortSpec.IsSorted /proofName:sort.merge_sort   /proofLocation:"$(pwd)/specs/sort/sortCorrect.dfy" /serverIpPortList:ipPorts.txt  $(pwd)/specs/sort/sortSpec.dfy &> experimentOutput/SortSpecCorrect/sortSpecCorrect_output.txt


mkdir experimentOutput/SortSpecCorrect/outputLogs
cp ./outputLogs/* experimentOutput/SortSpecCorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Sort Spec (Correct) - output found in ./experimentOutput/SortSpecCorrect/sortSpecCorrect_output.txt \n"

# --------------

echo -e "Starting Mutation Testing for Sort Spec (Incorrect)"

mkdir experimentOutput/SortSpecIncorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:sortSpec.IsSorted /proofName:sort.sortWrong   /proofLocation:"$(pwd)/specs/sort/sortIncorrect.dfy" /serverIpPortList:ipPorts.txt  $(pwd)/specs/sort/sortSpec.dfy &> experimentOutput/SortSpecIncorrect/sortSpecIncorrect_output.txt


mkdir experimentOutput/SortSpecIncorrect/outputLogs
cp ./outputLogs/* experimentOutput/SortSpecIncorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Sort Spec (Incorrect) - output found in ./experimentOutput/SortSpecIncorrect/sortSpecIncorrect_output.txt \n"

# --------------

echo -e "Starting Mutation Testing for Binary Search (Correct)"

mkdir experimentOutput/BSearchSpecCorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:searchSpec.searchSpecIncorrectV2 /proofName:BinarySearch.BinarySearch   /proofLocation:"$(pwd)/specs/search/searchCorrect.dfy" /serverIpPortList:ipPorts.txt  $(pwd)/specs/search/searchSpec.dfy &> experimentOutput/BSearchSpecCorrect/bsearchSpecCorrect_output.txt


mkdir experimentOutput/BSearchSpecCorrect/outputLogs
cp ./outputLogs/* experimentOutput/BSearchSpecCorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Sort Spec (Incorrect) - output found in ./experimentOutput/BSearchSpecCorrect/bsearchSpecCorrect_output.txt \n"

# --------------

echo -e "Starting Mutation Testing for Binary Search (Incorrect)"

mkdir experimentOutput/BSearchSpecIncorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:searchSpec.searchSpecIncorrectV2 /proofName:BinarySearch.BinarySearchIncorrect   /proofLocation:"$(pwd)/specs/search/searchIncorrect.dfy" /serverIpPortList:ipPorts.txt  $(pwd)/specs/search/searchSpec.dfy &> experimentOutput/BSearchSpecIncorrect/bsearchSpecIncorrect_output.txt

mkdir experimentOutput/BSearchSpecIncorrect/outputLogs
cp ./outputLogs/* experimentOutput/BSearchSpecIncorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Sort Spec (Incorrect) - output found in ./experimentOutput/BSearchSpecIncorrect/bsearchSpecCorrect_output.txt \n"

# --------------

echo -e "Starting Mutation Testing for KV SM (Correct)"

mkdir experimentOutput/KVSMSpecCorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:MapSpec.QueryOp /proofName:RefinementProof.RefinementNext     /proofLocation:"$(pwd)/specs/kvsm/kv_proof_correctProto_incorrectProof.dfy" /serverIpPortList:ipPorts.txt  /mutationRootName:MapSpec.Next /IsStateMachine  $(pwd)/specs/kvsm/kvSmSpecIncorrect.dfy &> experimentOutput/KVSMSpecCorrect/kvmsmSpecCorrect_output.txt
 

mkdir experimentOutput/KVSMSpecCorrect/outputLogs
cp ./outputLogs/* experimentOutput/KVSMSpecCorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for KV SM (Correct) - output found in ./experimentOutput/KVSMSpecCorrect/kvmsmSpecCorrect_output.txt \n"

# --------------

echo -e "Starting Mutation Testing for KV SM (Incorrect)"

mkdir experimentOutput/KVSMSpecIncorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:MapSpec.QueryOp /proofName:RefinementProof.RefinementNext     /proofLocation:"$(pwd)/specs/kvsm/kv_proof_incorrect.dfy" /serverIpPortList:ipPorts.txt  /mutationRootName:MapSpec.Next /IsStateMachine  $(pwd)/specs/kvsm/kvSmSpecIncorrect.dfy &> experimentOutput/KVSMSpecIncorrect/kvmsmSpecIncorrect_output.txt 

mkdir experimentOutput/KVSMSpecIncorrect/outputLogs
cp ./outputLogs/* experimentOutput/KVSMSpecIncorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for KV SM (Incorrect) - output found in ./experimentOutput/KVSMSpecIncorrect/kvmsmSpecIncorrect_output.txt \n"

# --------------

echo -e "Starting Mutation Testing for Token-wre (Correct)"

mkdir experimentOutput/Token-wreSpecCorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:wrapperModule.TokenRevertExternal.GInv /proofName:wrapperModule.proofStub /mutationRootName:wrapperModule.TokenRevertExternal.GInv    /serverIpPortList:ipPorts.txt $(pwd)/specs/token-wre/token-with-revert-external.dfy &> experimentOutput/Token-wreSpecCorrect/token-wreCorrect_output.txt

mkdir experimentOutput/Token-wreSpecCorrect/outputLogs
cp ./outputLogs/* experimentOutput/Token-wreSpecCorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Token-wre (Correct)- output found in ./experimentOutput/Token-wreSpecCorrect/token-wreCorrect_output.txt \n"

# --------------

echo -e "Starting Mutation Testing for Token-wre (Incorrect)"

mkdir experimentOutput/Token-wreSpecIncorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:wrapperModule.TokenRevertExternal.GInv /proofName:wrapperModule.proofStub /mutationRootName:wrapperModule.TokenRevertExternal.GInv    /serverIpPortList:ipPorts.txt $(pwd)/specs/token-wre/tokenIncorrect.dfy &> experimentOutput/Token-wreSpecIncorrect/token-wreIncorrect_output.txt

mkdir experimentOutput/Token-wreSpecIncorrect/outputLogs
cp ./outputLogs/* experimentOutput/Token-wreSpecIncorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Token-wre (Incorrect)- output found in ./experimentOutput/Token-wreSpecIncorrect/token-wreIncorrect_output.txt \n"

# --------------


echo -e "Starting Mutation Testing for SimpleAuction-wre (Correct)"

mkdir experimentOutput/SimpleAuction-wreSpecCorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:wrapperModule.SimpleAuctionRevertExternal.GInv /proofName:wrapperModule.SimpleAuctionRevertExternal.proofStub /mutationRootName:wrapperModule.SimpleAuctionRevertExternal.GInv    /serverIpPortList:ipPorts.txt $(pwd)/specs/simpleAuction-wre/SimpleAuction-with-revert-external.dfy &> experimentOutput/SimpleAuction-wreSpecCorrect/SimpleAuction-wreCorrect_output.txt

mkdir experimentOutput/SimpleAuction-wreSpecCorrect/outputLogs
cp ./outputLogs/* experimentOutput/SimpleAuction-wreSpecCorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Token-wre (Correct)- output found in ./experimentOutput/SimpleAuction-wreSpecCorrect/SimpleAuction-wreCorrect_output.txt \n"

# --------------


echo -e "Starting Mutation Testing for SimpleAuction-wre (Incorrect)"

mkdir experimentOutput/SimpleAuction-wreSpecIncorrect

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:wrapperModule.SimpleAuctionRevertExternal.GInv /proofName:wrapperModule.SimpleAuctionRevertExternal.proofStub /mutationRootName:wrapperModule.SimpleAuctionRevertExternal.GInv    /serverIpPortList:ipPorts.txt $(pwd)/specs/simpleAuction-wre/auctionIncorrect.dfy &> experimentOutput/SimpleAuction-wreSpecIncorrect/SimpleAuction-wreIncorrect_output.txt

mkdir experimentOutput/SimpleAuction-wreSpecIncorrect/outputLogs
cp ./outputLogs/* experimentOutput/SimpleAuction-wreSpecIncorrect/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Token-wre (Incorrect)- output found in ./experimentOutput/SimpleAuction-wreSpecIncorrect/SimpleAuction-wreIncorrect_output.txt \n"

# --------------

# --------------
# Open Source
# --------------

echo -e "Starting Mutation Testing for Div"

mkdir experimentOutput/Div

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /noCheating:1 /mutationTarget:div.wrapper /proofName:div.divRem /mutationRootName:div.wrapper    /proofLocation:"$(pwd)/specs/div/div.dfy" /serverIpPortList:ipPorts.txt /inPlaceMutation /functionMethodFlag $(pwd)/specs/div/div.dfy &> experimentOutput/Div/Div_output.txt

mkdir experimentOutput/Div/outputLogs
cp ./outputLogs/* experimentOutput/Div/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Div - output found in ./experimentOutput/Div/Div_output.txt \n"

# # --------------

echo -e "Starting Mutation Testing for NthHarmonic"

mkdir experimentOutput/NthHarmonic

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /noCheating:1 /mutationTarget:nHarm.wrapper /proofName:nHarm.NthHarmonic /mutationRootName:nHarm.wrapper    /proofLocation:"$(pwd)/specs/nthHarmonic/nHarmonic.dfy" /serverIpPortList:ipPorts.txt /inPlaceMutation /functionMethodFlag $(pwd)/specs/nthHarmonic/nHarmonic.dfy &> experimentOutput/NthHarmonic/NthHarmonic_output.txt
mkdir experimentOutput/NthHarmonic/outputLogs
cp ./outputLogs/* experimentOutput/NthHarmonic/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for NthHarmonic - output found in ./experimentOutput/NthHarmonic/NthHarmonic_output.txt \n"


# --------------
# DAISY-NSFD
# --------------

# clone daisy-nfsd repo and reset to commit hash used in initial experiments. 
echo -e "Cloning Daisy-nsfd Repo into ./specs/daisy-nfsd"

cd specs/daisy-nfsd
git clone https://github.com/mit-pdos/daisy-nfsd.git
cd daisy-nfsd
git reset --hard 98434db21451b76c700dcf5783b2bca00a63c132

patch src/fs/dir_fs.dfy ../daisy.patch
cd ../../..
echo $(pwd)
mkdir experimentOutput/daisy-nfsd

# --------------
echo -e "Starting Mutation Testing for Daisy-nsfd WRITE"

mkdir experimentOutput/daisy-nfsd/WRTIE
./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /noCheating:1 /arith:5 /mutationTarget:DirFs.DirFilesys.wrapper /proofName:DirFs.DirFilesys.WRITE /mutationRootName:DirFs.DirFilesys.wrapper    /proofLocation:"$(pwd)/specs/daisy-nfsd/daisy-nfsd/src/fs/dir_fs.dfy" /serverIpPortList:ipPorts.txt /inPlaceMutation $(pwd)/specs/daisy-nfsd/daisy-nfsd/src/fs/dir_fs.dfy &> experimentOutput/daisy-nfsd/WRTIE/daisy-nfsd-WRTIE_output.txt

mkdir experimentOutput/daisy-nfsd/WRTIE/outputLogs
cp ./outputLogs/* experimentOutput/daisy-nfsd/WRTIE/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Daisy-nsfd WRITE - output found in ./experimentOutput/daisy-nfsd/WRTIE/daisy-nfsd-WRTIE_output.txt \n"

# --------------

echo -e "Starting Mutation Testing for Daisy-nsfd GETATTR"

mkdir experimentOutput/daisy-nfsd/GETATTR
./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /noCheating:1 /arith:5 /mutationTarget:DirFs.DirFilesys.wrapper /proofName:DirFs.DirFilesys.GETATTR /mutationRootName:DirFs.DirFilesys.wrapper    /proofLocation:"$(pwd)/specs/daisy-nfsd/daisy-nfsd/src/fs/dir_fs.dfy" /serverIpPortList:ipPorts.txt /inPlaceMutation $(pwd)/specs/daisy-nfsd/daisy-nfsd/src/fs/dir_fs.dfy &> experimentOutput/daisy-nfsd/GETATTR/daisy-nfsd-GETATTR_output.txt

mkdir experimentOutput/daisy-nfsd/GETATTR/outputLogs
cp ./outputLogs/* experimentOutput/daisy-nfsd/GETATTR/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for Daisy-nsfd GETATTR - output found in ./experimentOutput/daisy-nfsd/GETATTR/daisy-nfsd-GETATTR_output.txt \n"


# --------------
# QBFT
# --------------

# clone qbft repo and reset to commit hash used in initial experiments. 
echo -e "Cloning QBFT Repo into ./specs/qbft"

cd specs/qbft
git clone https://github.com/Consensys/qbft-formal-spec-and-verification.git
cd qbft-formal-spec-and-verification
git reset --hard 1630128e7f5468c08983d08064230422d9337805
patch dafny/ver/L1/theorems.dfy ../theorems.patch

cd ../../..
echo $(pwd)
mkdir experimentOutput/qbft/

# --------------

echo -e "Starting Mutation Testing for qbft NetworkInit"

mkdir experimentOutput/qbft/NetworkInit

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:L1_SpecNetwork.NetworkInit /proofName:L1_Theorems.lemmaConsistencyAndStability    /proofLocation:"$(pwd)/specs/qbft/qbft-formal-spec-and-verification/dafny/ver/L1/theorems.dfy" /serverIpPortList:ipPorts.txt /holeEvalCons:L1_InstrDSStateInvariantsDefs.allIndInv /holeEvalBase:L1_DistributedSystem.DSInit $(pwd)/specs/qbft/qbft-formal-spec-and-verification/dafny/ver/L1/distr_system_spec/network.dfy &> experimentOutput/qbft/NetworkInit/qbft-networkInit_output.txt

mkdir experimentOutput/qbft/NetworkInit/outputLogs
cp ./outputLogs/* experimentOutput/qbft/NetworkInit/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for qbft NetworkInit - output found in ./experimentOutput/qbft/NetworkInit/qbft-networkInit_output.txt \n"

# --------------

echo -e "Starting Mutation Testing for qbft AdversaryNext"

mkdir experimentOutput/qbft/AdversaryNext

./Binaries/Dafny /compile:0 /timeLimit:3520 /trace /arith:5 /noCheating:1 /mutationTarget:L1_Adversary.AdversaryNext /proofName:L1_Theorems.lemmaConsistencyAndStability    /proofLocation:"$(pwd)/specs/qbft/qbft-formal-spec-and-verification/dafny/ver/L1/theorems.dfy" /serverIpPortList:ipPorts.txt /holeEvalCons:L1_InstrDSStateInvariantsDefs.allIndInv /holeEvalBase:L1_InstrumentedSpecs.DSInstrNextNodeMultiple $(pwd)/specs/qbft/qbft-formal-spec-and-verification/dafny/ver/L1/distr_system_spec/adversary.dfy &> experimentOutput/qbft/AdversaryNext/qbft-adversaryNext_output.txt

mkdir experimentOutput/qbft/AdversaryNext/outputLogs
cp ./outputLogs/* experimentOutput/qbft/AdversaryNext/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for qbft AdversaryNext - output found in ./experimentOutput/qbft/AdversaryNext/qbft-adversaryNext_output.txt \n"

# --------------

echo -e "Starting Mutation Testing for qbft AdversaryInit"

mkdir experimentOutput/qbft/AdversaryInit

./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:L1_Adversary.AdversaryInit /proofName:L1_Theorems.lemmaConsistencyAndStability    /proofLocation:"$(pwd)/specs/qbft/qbft-formal-spec-and-verification/dafny/ver/L1/theorems.dfy" /serverIpPortList:ipPorts.txt /holeEvalCons:L1_InstrDSStateInvariantsDefs.allIndInv /holeEvalBase:L1_InstrumentedSpecs.InstrDSInit $(pwd)/specs/qbft/qbft-formal-spec-and-verification/dafny/ver/L1/distr_system_spec/adversary.dfy &> experimentOutput/qbft/AdversaryInit/qbft-adversaryInit_output.txt

mkdir experimentOutput/qbft/AdversaryInit/outputLogs
cp ./outputLogs/* experimentOutput/qbft/AdversaryInit/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for qbft AdversaryInit - output found in ./experimentOutput/qbft/AdversaryInit/qbft-adversaryInit_output.txt \n"


# --------------
# DVT
# --------------

# clone dvt repo and reset to commit hash used in initial experiments. 
echo -e "Cloning DVT Repo into ./specs/dvt"

cd specs/dvt
git clone https://github.com/Consensys/distributed-validator-formal-specs-and-verification.git

cd distributed-validator-formal-specs-and-verification
git reset --hard fed55f5ea4d0ebf1b7d21b2c6fc1ecb79b5c3dd3
patch src/specs/consensus/consensus.dfy ../consensus.patch
patch src/specs/dv/dv_attestation_creation.dfy ../dvAttestationCreation.patch

cd ../../..
echo $(pwd)
mkdir experimentOutput/dvt/


# --------------

echo -e "Starting Mutation Testing for dvt AdversaryNext"

mkdir experimentOutput/dvt/AdversaryNext

./Binaries/Dafny /compile:0 /noCheating:1 /trace /timeLimit:10000 /mutationTarget:DV.NextAdversary /proofName:No_Slashable_Attestations_Main_Theorem.lem_non_slashable_attestations    /proofLocation:"$(pwd)/specs/dvt/distributed-validator-formal-specs-and-verification/src/proofs/no_slashable_attestations/main_theorem.dfy"  /serverIpPortList:ipPorts.txt $(pwd)/specs/dvt/distributed-validator-formal-specs-and-verification/src/specs/dv/dv_attestation_creation.dfy &> experimentOutput/dvt/AdversaryNext/dvt-adversaryNext_output.txt

mkdir experimentOutput/dvt/AdversaryNext/outputLogs
cp ./outputLogs/* experimentOutput/dvt/AdversaryNext/outputLogs
rm ./outputLogs/*

echo -e "DONE Mutation Testing for dvt AdversaryNext - output found in ./experimentOutput/dvt/AdversaryNext/dvt-adversaryNext_output.txt \n"

