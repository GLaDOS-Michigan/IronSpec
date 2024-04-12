#!/bin/bash
output_dir=grpc_nodes_output;
mkdir -p ${output_dir}
Username="$1"
ListOfNodeIds=""
ListOfIps=""
RootIP=""
declare -i numberOfNodes=0
for i in `seq 2 $#`
do
    ListOfNodeIds+="${!i} "
    numberOfNodes+=1
done
echo ListOfNodeIds = $ListOfNodeIds
echo Username = $Username

for id in $ListOfNodeIds; do
    echo "Getting IP for Node ID = $id"
    ListOfIps+="$(ssh $Username@clnode${id}.clemson.cloudlab.us ifconfig | grep "130.127" | awk '{print $2}') "
    ListOfIps+=" "
done

cd ..
ROOTPWD=$(pwd)
echo "pwd is $ROOTPWD"
cd -
for ip in $ListOfIps; do
    # copying dafny binary to grpc servers
    echo "starting server at $ip " &
    # ssh $Username@${ip} "(cd $ROOTPWD/IronSpec-dafny-grpc-server; ls)"
    ssh $Username@${ip} "(cd $ROOTPWD/IronSpec-dafny-grpc-server; ./bazel-bin/src/server -v -d $ROOTPWD/dafny-holeEval/Binaries/Dafny & disown -a)" &> ${output_dir}/node_${ip}.txt &  
done

for((cnt=0;cnt<$numberOfNodes;cnt=cnt+1))
do
    wait -n
    echo "One process with pid=$! end with Exit status: $?"
done

