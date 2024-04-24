#!/bin/bash
echo "Configuring other scripts... "
echo "Personalizing scripts with [username] [list_of_node_ids]"

#Config-Variables
output_dir=grpc_nodes_output;
output_logs=outputLogs;
mkdir -p ${output_dir}
mkdir -p ${output_logs}
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

#Calculate IP addresses of nodes and create ipPorts.txt
rm -f ipPorts.txt
touch ipPorts.txt

for id in $ListOfNodeIds; do
    echo "Getting IP for Node ID = $id"
    nodeId="$(ssh $Username@clnode${id}.clemson.cloudlab.us ifconfig | grep "130.127" | awk '{print $2}')"
    echo "$nodeId:50051" >> ipPorts.txt
    ListOfIps+="$nodeId"
    ListOfIps+=" "
done

for ip in $ListOfIps; do
    echo "Testing ssh connection to ID = $ip"
    ssh $Username@${ip} ls;
done

cd ..
ROOTPWD=$(pwd)
echo "pwd is $ROOTPWD"
cd -


echo "---- Cloning  grpc server repo ----"

cd ..
# clone grpc server repo
git clone https://github.com/GLaDOS-Michigan/IronSpec-dafny-grpc-server.git
cd -
#add user-specific elements
sed "s/username/$Username/" $ROOTPWD/IronSpec/Source/Dafny/DafnyVerifier.cs > ./tmp.cs && mv ./tmp.cs $ROOTPWD/IronSpec/Source/Dafny/DafnyVerifier.cs
# make z3
cd IronSpec/
make z3-ubuntu

echo "---- Installing And Building Dependencies ----"

for ip in $ListOfIps; do
    echo "-- installing dependencies for node $ip -- "
    # install global dependencies
    ssh $Username@${ip} "(cd $ROOTPWD/IronSpec; ./setup/node_prep.sh)";
    ssh $Username@${ip} "(cd $ROOTPWD/IronSpec; ./setup/install_dotnet_ubuntu_20.04.sh)";
    # #build IRONSPEC
    ssh $Username@${ip} "(cd $ROOTPWD/IronSpec; make exe)"
    # build dafny grpc server
    ssh $Username@${ip} "(cd $ROOTPWD/IronSpec-dafny-grpc-server; bazel-4.0.0 build --cxxopt="-g" --cxxopt="--std=c++17" //src:server)";
done

echo "---- Done Installing Dependencies ----"


echo "---- Starting Dafny GRPC Server(s) ----"

for ip in $ListOfIps; do
    echo "grpc server started at $ip on port :50051 " &
    ssh $Username@${ip} "(cd $ROOTPWD/IronSpec-dafny-grpc-server; ./bazel-bin/src/server -v -d $ROOTPWD/IronSpec/Binaries/Dafny & disown -a)" &> ${output_dir}/node_${ip}.txt &  
done

for((cnt=0;cnt<$numberOfNodes;cnt=cnt+1))
do
    wait -n
    echo "One process with pid=$! end with Exit status: $?"
done



echo "IronSpec setup done!"