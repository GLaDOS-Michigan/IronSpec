#!/bin/bash

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


for ip in $ListOfIps; do
    # copying dafny binary to grpc servers
    echo "stopping server at $ip " &
    # ssh $Username@${ip} "(cd $ROOTPWD/IronSpec-dafny-grpc-server; ls)"
    ssh $Username@${ip} "(echo "pid=$(pidof server Dafny)"; sudo killall server Dafny)"  
done
