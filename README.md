# IronSpec

Specification Testing framework prototype for [Dafny Specificiatons](https://github.com/dafny-lang/dafny)

# Dependencies

dafny-grpc-server (link tbd - talk to armin)
commit # fa006d6f9be52069154f537cc42f4e905a4e6adc

Dotnet 


# Setup

Using cloudlab:

IronSpec is designed to use one root node and `n` distributed nodes for verification. The root node is responsible for generating the specification mutations and verification conditions, the `n` separate nodes are used to parallelize the verification checking. The `n` additional nodes are not necessary to run IronSpec, but are used to help increase the performance. 

In cloudlab, the default profile is titled "IronSpecConfigNodes" and is configured to use 21, c8220 nodes, but this can be modified in the experiment instantiation.

After creating a cloudlab experiment, make note of all the id's of the nodes from the Node column in the experiment page. For example the id of Node "clnode008" is 008.


make sure to replace placeholder values in appropriate locations in each of the following scripts. (i.e. [username], [root_ip], [list_of_ips], [list_of_node_ids])
##### Find ip addresses

Note the IP addresses of the machines intended to use inFind the ip addresses of all nodes in the experiment, using running `echoIp.sh` in `/setup` from a local machine will help.

##### Setup ssh keys

Populate `nodeRS.sh` in `/setup` with the IP addresses found in the previous step. `rootIpPort` should be the Ip of the root node, and the remaining IP addresses should be entered on line 8 (including the root).

To test if this step has worked up to this point, run `testRS.sh` in `/setup` from the root node in the cloudlab experiment (the [list_of_node_ids] on line 6 should contain the ids of all nodes in the experiment excluding the root node). 

##### Setup cloudlab nodes

Run `/proj/spectesting-PG0/node_prep.sh` in each cloudlab node.
Run `/proj/spectesting-PG0/install_dotnet_ubuntu_20.04.sh` in each cloudlab node.
(these files are also included in `/setup` if not using cloudlab)[todo]


Install the dafny GRPC server on each node (also ):
`/proj/spectesting-PG0/dafny-grpc-server; bazel-4.0.0 build --cxxopt="-g" --cxxopt="--std=c++17" //src:server`

The script `./setup/nodeSetup.sh` can assist in calling these scripts in each node in the experiment.

Start the grpc servers - `/setup/run_grpc.sh` (this is best done using `screen` command to make sure that the grpc servers remain running)

[to check if the grpc server is running `pidof server Dafny`]

edit ipPortOneNode.txt to include the ip addresses of all the other nodes in the experiment  with port `:50051`
# Run Mutation Testing

The general command to run mutation testing follow this form:

`./Binaries/Dafny` [Standard Dafny Arguments] [IronSpec Arguemnts] [full path to the file containing mutation target] `&> output.txt`

For example:
run the following command from the root node
```
./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /holeEval:maxExample.maxSpec /proofName:maxTest.maxT /holeEvalRunOnce /holeEvalDepth:2 /proofLocation:"/proj/spectesting-PG0/dafny-holeEval/multiMaxExFull/lemmaMaxTestCorrect.dfy" /holeEvalServerIpPortList:ipPortOneNode.txt /proj/spectesting-PG0/dafny-holeEval/multiMaxExFull/maxPredMutations.dfy &> output.txt
```
After executing this command, see the output in a file named `output.txt` and the tail of the output will look like this:

```
...
--- END Mutation Classifications -- 

Elapsed Time (Classifications) is 18528 ms
TOTAL Elapsed Time is 31231 ms
root = (0):(a > b ==> c == a) && (b + 1 > a ==> c == b)
18 :: 24 :: 25 :: 38 :: 42 :: 48 :: 49 :: 60 :: 69 :: 73 :: 75 
---
Total Alive Mutations = 1

```
This output indicates that there is a single alive mutation to investigate `(a > b ==> c == a) && (b + 1 > a ==> c == b)` 

Full experiment logs can be found in `/outputLogs` which will contain the logs for each mutation and the intermediary files genereated for the different mutation testing passes. Any `.txt` file contains the output from the dafny verifier for each mutation. There are many `.dfy` files genereated to test the different mutation passes (i.e. weaker, vac, full, classify.)


Running the mutation framework for a method as the mutation target 


./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /noCheating:1 /arith:5 /holeEval:DirFs.DirFilesys.wrapper /proofName:DirFs.DirFilesys.WRITE /mutationRootName:DirFs.DirFilesys.wrapper  /holeEvalRunOnce /holeEvalDepth:2 /proofLocation:"/proj/spectesting-PG0/dafny-holeEval/examples/daisy-nfsd/src/fs/dir_fs.dfy" /holeEvalServerIpPortList:ipPortOneNode.txt /inPlaceMutation /proj/spectesting-PG0/dafny-holeEval/examples/daisy-nfsd/src/fs/dir_fs.dfy &> output.txt


# Run The Automatic Sanity Checking (ASC)

The general command to run mutation testing follow this form:

`./Binaries/Dafny` [Standard Dafny Arguments] [IronSpec Arguemnts] `/checkInputAndOutputSpecified` [full path to the file containing mutation target] `&> output.txt`

```
./Binaries/Dafny /compile:0 /timeLimit:1520 /trace /arith:5 /noCheating:1 /holeEval:testWrapper.SATSolver.test /proofName:testWrapper.SATSolver.start /mutationRootName:testWrapper.SATSolver.test /holeEvalRunOnce /holeEvalDepth:2 /proofLocation:"/proj/spectesting-PG0/dafny-holeEval/examples/truesat/truesat_src/solver/solver.dfy" /holeEvalServerIpPortList:ipPortOneNode.txt /checkInputAndOutputSpecified /proj/spectesting-PG0/dafny-holeEval/examples/truesat/truesat_src/solver/solver.dfy &> output.txt
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
|/holeEvalRunOnce| |
|/holeEvalDepth:2 | | 
| /checkInputAndOutputSpecified | Argument to indicate the use of the ASC. When using this flag, /holeEval and /mutationRootName should be set to a predicate in the same file, this is irrelevant. /proofName should be set to the method that is being tested with the ASC  | 

