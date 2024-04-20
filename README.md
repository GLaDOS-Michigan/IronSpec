# IronSpec

Specification Testing framework prototype for [Dafny](https://github.com/dafny-lang/dafny) Specificiatons. 

IronSpec brings together three different spec-testing techniques; Automatic Sanity Checking(ASC), automatic specification mutation testing, and a Methodology for writing Spec Testing Proofs (STPs).


# Dependencies

* [IronSpec-dafny-grpc-server](https://github.com/GLaDOS-Michigan/IronSpec-dafny-grpc-server)
* openjdk-13-jdk 
* gcc-8
* g++-8
* bazel-4.0.0
* dotnet-6 

NOTE: All dependencies can be installed by running `./setup/configureIronspec.sh`

# Setup

The recomended environment to to run IronSpec is using [CloudLab](https://www.cloudlab.us/):

IronSpec is designed to use one root node and `n` distributed nodes for verification performance. The root node is responsible for generating the specification mutations and verification conditions, the `n` separate nodes are used to parallelize checking verification conditions. The `n` additional nodes are not necessary to run IronSpec, they are used to help increase the performance and reduce experiment runtime. 

In cloudlab, a default profile is available titled "IronSpecConfigNodes" and is configured to use 21, c8220 nodes - this can be modified in the experiment instantiation to change the configuration. A copy of this profile can be found in `./setup.cloudlabProfile.txt`

After creating a cloudlab experiment, make note of all the id's of the nodes from the Node column in the experiment page. For example the id of Node "clnode008" is 008.

<!-- make sure to replace placeholder values in appropriate locations in each of the following scripts. (i.e. [username], [root_ip], [list_of_ips], [list_of_node_ids]) -->
<!-- ##### Find ip addresses

Note the IP addresses of the machines intended to use inFind the ip addresses of all nodes in the experiment, using running `echoIp.sh` in `/setup` from a local machine will help. -->

##### Setup ssh keys

The first step is to set up the ssh keys between all of the cloudlab nodes. Do this from a local machine (non-cloudlab). 

Run `./setup/configureSSHKeys.sh [username] [list_of_node_ids]`

`username` is your cloudlab username
`list_of_node_ids` is a list of the cloudlab node ids seperated by spaces. 

For example if the list of nodes included, run: `clnode008 and clnode015` - `./setup/configureSSHKeys.sh [username] 008 015`

<!-- Populate `nodeRS.sh` in `/setup` with the IP addresses found in the previous step. `rootIpPort` should be the Ip of the root node, and the remaining IP addresses should be entered on line 8 (including the root).

To test if this step has worked up to this point, run `testRS.sh` in `/setup` from the root node in the cloudlab experiment (the [list_of_node_ids] on line 6 should contain the ids of all nodes in the experiment excluding the root node).  -->

##### Setup cloudlab nodes

Run `./setup/configureIronSpec.sh [username] [list_of_node_ids]`

From the cloudlab node that will act as the "root" node for the experiment. (i.e the node with the smallest id)

This script will install all the dependencies on each node in the experiment, build IronSpec, and start the dafny-GRPC servers on all of the nodes at port `:50051`. This step may take some time to complete.

If there is ever a need to start or stop the dafny-GRPC servers run either:
`./setup/startDafnyServers.sh [username] [list_of_node_ids]`
`./setup/stopDafnyServers.sh [username] [list_of_node_ids]`


> **_NOTE:_**  to check if a grpc server is running `pidof server Dafny`



# Specs

The IronSpec prototype is designed to faciliate testing Dafny specifications. Examples of specifications can be found in the `./specs`. 

This directory conists of 14 specifications, 6 in-house specifications and 8 specifications from open source systems.

The 6 in-house specifications, max, sort, binary search, key-value state machine, token-wre, simpleAuction-wre, and two open source specs, div and NthHarmonic are included in whole. div and NthHarmonic are transcribed to dafny from ["Exploring automatic specification repair in dafny programs"](https://conf.researchr.org/details/ase-2023/ase-2023--workshop--asyde/8/Exploring-Automatic-Specification-Repair-in-Dafny-Programs). Token-wre and simpleAuction-wre were taken from ["Deductive verification
of smart contracts with dafny"](https://arxiv.org/abs/2208.02920) with small modifications to artificailly introduce bugs into the corresponding specs. 

In the following table are the list of all specs. For the open-source specs, the link corresponds to the initial commit that was used when testing the spec with IronSpec. 

| Spec Name             | Source   | 
| :----------------     | :------: |
| Max                   |  `./specs`   | 
| Sort                  |  `./specs`   | 
| Binary Search         |  `./specs`   | 
| Key-Value Store SM    |  `./specs`   | 
| token-wre             |  `./specs`   |
| simpleAuction-wre     |  `./specs`   | 
| div                   | `./specs`    |  
| NthHarmonic           |  `./specs`   |
| [QBFT](https://github.com/Consensys/qbft-formal-spec-and-verification/tree/1630128e7f5468c08983d08064230422d9337805) |  external    |
| [Distributed Validator](https://github.com/Consensys/distributed-validator-formal-specs-and-verification/tree/fed55f5ea4d0ebf1b7d21b2c6fc1ecb79b5c3dd3) |  external   |
| [daisy-nfsd](https://github.com/mit-pdos/daisy-nfsd/tree/98434db21451b76c700dcf5783b2bca00a63c132)            |  external   |
| [TrueSat](https://github.com/andricicezar/truesat/tree/62f52fd82709b888fa604f20297f83572c8592ae)               |  external   |
| [Eth2.0](https://github.com/Consensys/eth2.0-dafny/tree/4e41de2866c8d017ccf4aaf2154471ffa722b308)                |  external   |
| [AWS ESDK](https://github.com/aws/aws-encryption-sdk-dafny/tree/eaa30b377be9c0c17aeae9fce11387b0fbccafba)              |  external   |

# Running IronSpec

To run all automatic experiments (Both Mutation Testing and Automatic Sanity Checking experiments) described in the OSDI paper, run: `./runExperiments.sh`

> **_NOTE:_** Running `./runExperiments.sh` will automatically clone all external specs into the `./spec` directory to the originally tested commit hash. Additionally small patches will be applied to external specs to accomodate for small changes between Dafny versions.

Output and logs for all experiments will be found in `./experimentOutput` split for each spec and for each experiment. The end of each file ending in `..._output.txt` for each experiemnt will show the final results.

**After `./runExperiments.sh` finishes, check `./experimentOutput/finalResults.txt` for a recreation of Tables 3 and 4 from the paper based on the results of running `./runExperiments.sh`** 

> **_NOTE:_**  The original experimental setup consisted of 1 root node and 20 nodes running the dafny-GRPC servers to parralleize checking verification conditions. Using a different configuration will impact the total time to run each experiment. The time difference is not strictly linear based on the number of nodes. There is a minimum time needed 


##### Mutation Testing 

The general command to run mutation testing follow this form:

`./Binaries/Dafny` [Standard Dafny Arguments] [IronSpec Arguemnts] [full path to the file containing mutation target] `&> output.txt`

For example to test the specification for a Max method (`/specs/max/maxPredMutations.dfy`), run the following command from the root node:
```
./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /holeEval:maxExample.maxSpec /proofName:maxTest.maxT /proofLocation:"$(pwd)/specs/max/lemmaMaxTestCorrect.dfy" /holeEvalServerIpPortList:ipPorts.txt $(pwd)/specs/max/maxPredMutations.dfy &> output.txt
```

After executing this command, see the output in a file named `output.txt` and the tail of the output will look like this:

```
...
...
--- END Mutation Classifications -- 

TOTAL Elapsed Time is 15749 ms
root = (0):(a > b ==> c == a) && (b + 1 > a ==> c == b)
7 :: 8 :: 42 :: 43 :: 44 :: 48 :: 50 :: 52 :: 60 :: 62 :: 63 
---
Total Alive Mutations = 1

```
This output indicates that there is a single alive mutation to investigate with ID 0 - `(a > b ==> c == a) && (b + 1 > a ==> c == b)` 

Full experiment logs can be found in `./outputLogs` which will contain the logs for each mutation and the intermediary files genereated for the different mutation testing passes. Any `.txt` file contains the output from the dafny verifier for each mutation. There are many `.dfy` files genereated to test the different mutation passes (i.e. weaker, vac, full, classification)

##### Automatic Sanity Checking (ASC)

The general command to run mutation testing follow this form:

`./Binaries/Dafny` [Standard Dafny Arguments] [IronSpec Arguemnts] `/checkInputAndOutputSpecified` [full path to the file containing mutation target] `&> output.txt`

```
./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /holeEval:testWrapper.SATSolver.test /proofName:testWrapper.SATSolver.start /mutationRootName:testWrapper.SATSolver.test /holeEvalRunOnce /holeEvalDepth:2 /proofLocation:"$(pwd)/specs/truesat/truesat_src/solver/solver.dfy" /holeEvalServerIpPortList:ipPortOneNode.txt /checkInputAndOutputSpecified $(pwd)/specs/truesat/truesat_src/solver/solver.dfy &> output.txt
```

# SpecTesting Proof(STPs) Examples

# Directory Structure

# IronSpec arguments

| Argument    | Description |
| -------- | ------- |
| /holeEval:[name] | Name of predicate for mutation target|
| /proofName:[name]  | Name of lemma for full end-to-end proof    |
| /proofLocation:[name] | Full path to `.dfy` file containing lemma targeted for /proofName     |
| /holeEvalServerIpPortList:[name]    | Name of `.txt` file containing the ip addresses and ports for other     |
|/inPlaceMutation  | This flag indicates that the mutation target is for a method with pre/post conditions rather than a predicate. In this case /proofName is the name of the method to mutate the spec and the proof to check. |  
| /mutationRootName:[name] | If the mutation target is different from the high-level safety property of the system, make sure to specify the high level safety property with this flag. | 
| /checkInputAndOutputSpecified | Argument to indicate the use of the ASC. When using this flag, /holeEval and /mutationRootName should be set to a predicate in the same file, this is irrelevant. /proofName should be set to the method that is being tested with the ASC  | 
