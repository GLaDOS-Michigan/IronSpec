# IronSpec

Specification Testing framework prototype for [Dafny](https://github.com/dafny-lang/dafny) Specifications. 

IronSpec brings together three different spec-testing techniques; Automatic Sanity Checking(ASC), automatic specification mutation testing, and a Methodology for writing Spec Testing Proofs (STPs).

# Dependencies

* [IronSpec-dafny-grpc-server](https://github.com/GLaDOS-Michigan/IronSpec-dafny-grpc-server)
* openjdk-13-jdk 
* gcc-8
* g++-8
* bazel-4.0.0
* dotnet-6 

The prototype is built off of Dafny v3.8.1


> **_NOTE:_** All dependencies will be installed when running `./setup/configureIronspec.sh` - detailed below
# Setup

The recommended environment to run IronSpec is using [CloudLab](https://www.cloudlab.us/):

IronSpec is designed to use one root node and `n` distributed nodes for verification performance. The root node is responsible for generating the specification mutations and verification conditions, the `n` separate nodes are used to parallelize checking verification conditions. The `n` additional nodes are not necessary to run IronSpec, they are used to help increase the performance and reduce experiment runtime. 

In cloudlab, a default profile is available titled "IronSpecConfigNodes" and is configured to use 21, c8220 nodes - this can be modified in the experiment instantiation to change the configuration. A copy of this profile can be found in `./setup/cloudlabProfile.txt`

After creating a cloudlab experiment, make note of all the unique numerical names of the nodes from the Node column in the experiment page List View. For example, the IDs of Nodes "clnode008" and "clnode059" are 008 and 059 respectively.

## Getting Started

To check basic functionality, it is sufficient to follow the following "Setup" steps with a single cloudlab node. After setup, to test to make sure that everything is installed and configured correctly, run `./runSimpleExperiments.sh` to run the mutation framework on a simple Max Spec found in: `./specs/max/maxSpec.dfy` and the Automatic Sanity Checker on `./specs/sort/sortMethod.dfy`


After executing this command, see the output in a file `./experimentOutput/MaxSpecCorrect/maxSpecCorrect_output.txt` and the tail of the output will look like this:

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

and the output in `./experimentOutput/sortASC/sortASC_output.txt` with a high serverity flag being raised `-- FLAG(HIGH) -- : NONE of Ensures depend on Any input parameters `

##### Clone repo
If using Cloudlab, clone this repo in the `/proj/[cloudlabProjectName]/` repo. This is shared disk space in Cloudlab and will speed up setup.

##### Setup SSH keys

The first step is to set up the SSH keys between all of the cloudlab nodes. (This is necessary even when using a single node)

**Make sure to follow these steps from a local machine (non-cloudlab).** 

Run `./setup/configureSSHKeys.sh [username] [list_of_node_ids]`

* `username`: cloudlab username
* `list_of_node_ids`: A list of the cloudlab node IDs separated by spaces. 

For example, if the list of nodes is included, run: `clnode008, clnode010 and clnode015` - `./setup/configureSSHKeys.sh [username] 008 010 015`


##### Setup cloudlab nodes

Run `./setup/cloudlabConfigureIronSpec.sh [username] [list_of_node_ids]` **From the cloudlab node that will act as the "root" node for the experiment. (i.e the node with the smallest id)**

(use `./setup/configureIronSpec.sh [username] [list_of_node_ids]` if the repo was not cloned this repo in `/proj/[cloudlabProjectName]/`)

This script will install all the dependencies on each node in the experiment, build IronSpec, and start the dafny-GRPC servers on all of the nodes at port `:50051`. This step may take some time to complete.

If there is ever a need to start or stop or see the PID of the dafny-GRPC servers run:
`./setup/startDafnyServers.sh [username] [list_of_node_ids]`
`./setup/stopDafnyServers.sh [username] [list_of_node_ids]`
`./setup/checkDafnyPID.sh [username] [list_of_node_ids]`


# Specs

The IronSpec prototype is designed to facilitate testing Dafny specifications. Examples of specifications can be found in the `./specs`. 

This directory consists of 14 specifications, 6 in-house specifications, and 8 specifications from open-source systems.

The 6 in-house specifications, max, sort, binary search, key-value state machine, token-wre, simpleAuction-wre, and two open source specs, div, and NthHarmonic are included in whole. div and NthHarmonic are transcribed to dafny from ["Exploring automatic specification repair in dafny programs"](https://conf.researchr.org/details/ase-2023/ase-2023--workshop--asyde/8/Exploring-Automatic-Specification-Repair-in-Dafny-Programs). Token-wre and simpleAuction-wre were taken from ["Deductive verification
of smart contracts with dafny"](https://arxiv.org/abs/2208.02920) with small modifications to artificially introduce bugs into the corresponding specs. 

In the following table is the list of all specs. For the open-source specs, the link corresponds to the initial commit that was used when testing the spec with IronSpec. 

| Spec Name | Source | 
| :---------------- | :------: |
| Max | `./specs` | 
| Sort | `./specs` | 
| Binary Search | `./specs` | 
| Key-Value Store SM | `./specs` | 
| token-wre | `./specs` |
| simpleAuction-wre | `./specs` | 
| div | `./specs` | 
| NthHarmonic | `./specs` |
| [QBFT](https://github.com/Consensys/qbft-formal-spec-and-verification/tree/1630128e7f5468c08983d08064230422d9337805) | external |
| [Distributed Validator](https://github.com/Consensys/distributed-validator-formal-specs-and-verification/tree/fed55f5ea4d0ebf1b7d21b2c6fc1ecb79b5c3dd3) | external |
| [daisy-nfsd](https://github.com/mit-pdos/daisy-nfsd/tree/98434db21451b76c700dcf5783b2bca00a63c132) | external |
| [TrueSat](https://github.com/andricicezar/truesat/tree/62f52fd82709b888fa604f20297f83572c8592ae) | external |
| [Eth2.0](https://github.com/Consensys/eth2.0-dafny/tree/4e41de2866c8d017ccf4aaf2154471ffa722b308) | external |
| [AWS ESDK](https://github.com/aws/aws-encryption-sdk-dafny/tree/eaa30b377be9c0c17aeae9fce11387b0fbccafba) | external |

# Running IronSpec

To run all automatic experiments (Both Mutation Testing and Automatic Sanity Checking experiments) described in the OSDI paper, run: `./runAllExperiments.sh`

It is recommended to run this command in a detached shell session since it will take some time to complete. For example:

```
screen -S runExperiments
./runAllExperiments.sh
[Ctrl-a][Ctrl-d] #This detaches the screen "runExperiments"

#To reattach
screen -R runExperiments
```

> **_NOTE:_** Running `./runExperiments.sh` will automatically clone all external specs into the `./spec` directory to the originally tested commit hash. Additionally, small patches will be applied to external specs to accommodate for small syntactical changes between Dafny versions.

Output and logs for each experiment will be found in `./experimentOutput` split into different sub-directories for each spec and each experiment. The tail of each produced file's name ending in `..._output.txt` for each experiment will show the final results.

**After `./runExperiments.sh` finishes, check `./experimentOutput/finalResults.txt` for recreation of Tables 3 and 4 from the paper based on the results of running `./runExperiments.sh`** 

> **_NOTE:_** The original experimental setup consisted of 1 root node and 20 nodes running the dafny-GRPC servers to parallelize checking verification conditions. Using a different configuration will impact the total time to run each experiment. The time difference is approximately linear based on the number of nodes; for example, running with 21 nodes an experiment taking approximately 160 min will be 3x as long when running the same experiment with 7 nodes. Having too few nodes may cause verification timeouts that result from overloading the various nodes, to run the full experiments it is recommended to have at least 7 nodes. There is a minimum bound for the time to run each experiment, as even if all verification tasks can be parallelized, larger systems like qbft and DVT still will take 1-2 hours for a full end-to-end proof. 

> **_NOTE:_** Some results in appearing in`./experimentOutput/finalResults.txt` may differ slightly from Table 4 in the included pdf. 
> * The time taken for each experiment will vary based on the number of nodes, the CPU load at each node, and the black-box nature of z3, so there may be some variance in timing.
> * The number of alive mutations for the `Div`spec will appear higher (8 vs 3). This is due to a limitation in the final step of the mutation framework that is incompatible with this type of spec in classifying alive mutations into a DAG. The result of reducing the 8 alive mutations to 3 is calculated manually with the assistance of Dafny. Details on how to achieve this are included in comments in `./specs/div/div.dfy`.
> * The number of generated mutations for QBFT NetworkInit, QBFT AdversaryInit, and DVT AdversaryNext should be 44, 35, and 110 respectively. These are updated results due to an improvement in avoiding producing duplicate mutations and will be adjusted in the camera-ready version. The difference in mutations is due to duplicate or logically equivalent mutations so does not affect the final number of alive mutations.
> * The number of alive mutations for QBFT AdversaryNext should be 4. This is the result of an increased timeout allowance for the mutation classification step - the same information is included in the 4 alive mutations as in the previous 7, so this improvement over the original values in table 4 as it further minimizes the manual effort to inspect more mutations. With this same timeout allowance increase, there is expected to be one more alive mutation for DVT AdversaryNext.
 


To run either the mutation testing experiments or just the ASC experiments, utilize either `./runMutationTestingExperiments.sh` or `./runASCExperiments.sh`. If running either of these, make sure to also run `./cleanExperimentOutput.sh` beforehand.

##### Mutation Testing 

The general command to run mutation testing follows this form:

`./Binaries/Dafny [Standard Dafny Arguments] [IronSpec Arguemnts] [full-path-to-the-file-containing-mutation-target] &> output.txt`

For example to test the specification for a Max method (`/specs/max/maxSpec.dfy`), run the following command from the root node:
```
./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /mutationTarget:maxExample.maxSpec /proofName:maxTest.maxT /proofLocation:"$(pwd)/specs/max/lemmaMaxTestCorrect.dfy" /holeEvalServerIpPortList:ipPorts.txt $(pwd)/specs/max/maxSpec.dfy &> output.txt
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
This output indicates that there is a single alive mutation(with ID 0) to investigate - `(a > b ==> c == a) && (b + 1 > a ==> c == b)` 

Full experiment logs can be found in `./outputLogs` which will contain the logs for each mutation and the intermediary files generated for the different mutation testing passes. Any `.txt` file contains the output from the dafny verifier for each mutation. There are many `.dfy` files generated to test the different mutation passes (i.e. weaker, vac, full, classification)

##### Automatic Sanity Checking (ASC)

The general command to run mutation testing follows this form:

`./Binaries/Dafny` [Standard Dafny Arguments] [IronSpec Arguemnts] `/checkInputAndOutputSpecified` [full path to the file containing mutation target] `&> output.txt`

```
./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /holeEval:testWrapper.SATSolver.test /proofName:testWrapper.SATSolver.start /mutationRootName:testWrapper.SATSolver.test /holeEvalRunOnce /holeEvalDepth:2 /proofLocation:"$(pwd)/specs/truesat/truesat_src/solver/solver.dfy" /holeEvalServerIpPortList:ipPortOneNode.txt /checkInputAndOutputSpecified $(pwd)/specs/truesat/truesat_src/solver/solver.dfy &> output.txt
```

# SpecTesting Proof(STPs) Examples
A brief description and some examples are included in `./STPS` 

STPs are just Dafny proofs, so running STPS requires no additional instrumentation other than just running Dafny. 


# IronSpec arguments

| Argument | Description |
| -------- | ------- |
| /mutationTarget:[name] | Full Name of predicate for mutation target. In Dafny, this includes the module name followed by the predicate name. For example, if the predicate's name is `spec` located in module `Example`, the full name is: `Example.spec` |
| /proofName:[name] | Name of lemma for full end-to-end proof. Also follows `Module.Name` format |
| /proofLocation:[name] | Full path to `.dfy` file containing lemma targeted for /proofName |
| /serverIpPortList:[name] | Name of `.txt` file containing the IP addresses and ports for other node end points. If configured using `./configureIronSpec.sh` a file named `ipPorts.txt` will be created with the correct formatting |
|/inPlaceMutation | This flag indicates that the mutation target is for a method with pre/post conditions rather than a predicate. In this case /proofName is the name of the method to mutate the spec and the proof to check. | 
| /mutationRootName:[name] | If the mutation target is different from the high-level safety property of the system, make sure to specify the high-level safety property with this flag. | 
| /checkInputAndOutputSpecified | Argument to indicate the use of the ASC. When using this flag, /holeEval and /mutationRootName should be set to a predicate in the same file, the contents of the predicate are irrelevant. /proofName should be set to the method that is being tested with the ASC | 
|/isRequires | Tests for mutations that are stronger than the original, rather than weaker|