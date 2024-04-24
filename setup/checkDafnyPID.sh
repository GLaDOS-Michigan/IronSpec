#!/bin/bash

Username="$1"
ListOfNodeIds=""
ListOfIps=""

for i in `seq 2 $#`
do
    ListOfNodeIds+="${!i} "
done
for id in $ListOfNodeIds; do
    echo $id $" -------------"&

    ssh $Username@clnode${id}.clemson.cloudlab.us "(pidof server Dafny;)"
    ssh $Username@clnode${id}.clemson.cloudlab.us "(pidof z3;)"

done
