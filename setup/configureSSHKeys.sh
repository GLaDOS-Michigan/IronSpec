#!/bin/bash
echo "Configuring SSH keys"

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
    nodeId="$(ssh $Username@clnode${id}.clemson.cloudlab.us ifconfig | grep "130.127" | awk '{print $2}')"
    ListOfIps+="$nodeId"
    ListOfIps+=" "
done


RootIP+="$(echo $ListOfIps | awk '{print $1}')"
echo "Configuring ssh keys between rootnode and all others..."
echo "rootIpPort = $RootIP"
(echo ""; echo ""; echo "";) | ssh $Username@${RootIP} "ssh-keygen -q"
tmpFile=$(mktemp)
echo $tmpFile
scp $Username@${RootIP}:.ssh/id_rsa.pub ${tmpFile}
for ipPort in $ListOfIps
do
    ssh $Username@${ipPort} ls
    scp ${tmpFile} $Username@${ipPort}:.ssh/rootSSHPublicKey.rsa
    ssh $Username@${ipPort} "cat .ssh/rootSSHPublicKey.rsa >> .ssh/authorized_keys";
done

echo "DONE"