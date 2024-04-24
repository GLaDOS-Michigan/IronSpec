#!/bin/bash
echo "Configuring other scripts... "
echo "Personalizing scripts with [username] [list_of_node_ids]"

#Config-Variables
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

#Calculate IP addresses of nodes and create ipPorts.txt
touch ipPorts.txt
# > ipPorts.txt
for id in $ListOfNodeIds; do
    echo "Getting IP for Node ID = $id"
    nodeId="$(ssh $Username@clnode${id}.clemson.cloudlab.us ifconfig | grep "130.127" | awk '{print $2}')"
    echo "$nodeId:50051" >> ipPorts.txt
    ListOfIps+="$nodeId"
    ListOfIps+=" "
done


# RootIP+="$(echo $ListOfIps | awk '{print $1}')"
# echo "Configuring ssh keys between rootnode and all others..."
# echo "rootIpPort = $RootIP"
# (echo ""; echo ""; echo "";) | ssh $Username@${RootIP} "ssh-keygen -q"
# tmpFile=$(mktemp)
# echo $tmpFile
# scp $Username@${RootIP}:.ssh/id_rsa.pub ${tmpFile}
# for ipPort in $ListOfIps
# do    
#     ssh $Username@${ipPort} ls
#     scp ${tmpFile} $Username@${ipPort}:.ssh/rootSSHPublicKey.rsa
#     ssh $Username@${ipPort} "cat .ssh/rootSSHPublicKey.rsa >> .ssh/authorized_keys";
# done

for ip in $ListOfIps; do
    echo "Testing ssh connection to ID = $id"
    ssh $Username@${ip} ls;
done

# echo "---- SSH Key configuration done ----"

echo "---- Installing And Building Dependencies ----"

cd ..
ROOTPWD=$(pwd)
echo "pwd is $ROOTPWD"
cd -
for ip in $ListOfIps; do
    echo "-- installing dependencies for node $ip -- "
    scp ./setup/node_prep.sh $Username@${ip}:$ROOTPWD/node_prep.sh
    ssh $Username@${ip} "(cd $ROOTPWD; ./node_prep.sh)";
    scp ./setup/install_dotnet_ubuntu_20.04.sh $Username@${ip}:$ROOTPWD/install_dotnet_ubuntu_20.04.sh;
    ssh $Username@${ip} "(cd $ROOTPWD; ./install_dotnet_ubuntu_20.04.sh)";

    # clone grpc server repo
    ssh $Username@${ip} "(cd $ROOTPWD; git clone https://github.com/GLaDOS-Michigan/IronSpec-dafny-grpc-server.git)";

    # build dafny grpc server
    ssh $Username@${ip} "(cd $ROOTPWD/IronSpec-dafny-grpc-server; bazel-4.0.0 build --cxxopt="-g" --cxxopt="--std=c++17" //src:server)";

    #clone IRONSPEC repo
    
    #add user-specific elements
    ssh $Username@${ip} "(sed "s/\[username\]/$Username/" $ROOTPWD/dafny-holeEval/Source/Dafny/DafnyVerifier.cs > ./tmp.cs && mv ./tmp.cs $ROOTPWD/dafny-holeEval/Source/Dafny/DafnyVerifier.cs)";
    #buld IRONSPEC
    ssh $Username@${ip} "(make exe)"

done

echo "---- Done Installing Dependencies ----"


echo "---- Starting Dafny GRPC Server(s) ----"

for ip in $ListOfIps; do
    # copying dafny binary to grpc servers
    echo "grpc server started at $ip on port :50051 " &
    # ssh $Username@${ip} "(cd $ROOTPWD/IronSpec-dafny-grpc-server; ls)"
    ssh $Username@${ip} "(cd $ROOTPWD/IronSpec-dafny-grpc-server; ./bazel-bin/src/server -v -d $ROOTPWD/dafny-holeEval/Binaries/Dafny & disown -a)" &> ${output_dir}/node_${ip}.txt &  
done

for((cnt=0;cnt<$numberOfNodes;cnt=cnt+1))
do
    wait -n
    echo "One process with pid=$! end with Exit status: $?"
done



# # # sed "s/[username]/$1/" ./setup/nodeRS.sh > tmp.sh && mv tmp.sh ./setup/nodeRS.sh
# # # sed "s/[username]/$1/" ./setup/nodeRS.sh > tmp.sh && mv tmp.sh ./setup/nodeRS.sh
# # # echo "Configuring DafnyVerifier.cs"




echo "IronSpec setup done!"