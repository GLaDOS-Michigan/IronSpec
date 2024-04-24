#!/bin/sh

sudo apt-get update
sudo apt -y install openjdk-13-jdk python3-pip libelf-dev swig graphviz build-essential git m4 scons zlib1g zlib1g-dev libprotobuf-dev protobuf-compiler libprotoc-dev libgoogle-perftools-dev python-dev python qemu-system-x86 python-six
sudo apt -y install build-essential libncurses-dev bison flex libssl-dev libelf-dev g++-8 g++-8-multilib
#sudo apt -y install docker docker.io
pip3 install pre-commit
sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-8 20
sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-8 20
#sudo ufw status verbose
#sudo ufw default deny incoming
#sudo ufw allow OpenSSH
#sudo ufw enable
#sudo /usr/local/etc/emulab/mkextrafs.pl /var/lib/docker

#sudo swapoff -a
#(echo "n"; echo ""; echo ""; echo ""; echo "+500G"; echo "Y"; echo "n"; echo ""; echo ""; echo ""; echo ""; echo "w";) | sudo fdisk /dev/sdb
#(echo "/dev/sdb1 swap swap defaults 0 0") | sudo tee -a /etc/fstab
#sudo mkfs.ext4 /dev/sdb1
#sudo mkfs.ext4 /dev/sdb2
#sudo mount /dev/sdb1 /usr/local
#sudo mkdir -p /var/lib/docker
#sudo mount /dev/sdb2 /var/lib/docker/
sudo apt -y install docker docker.io

sudo apt install -y apt-transport-https curl gnupg
curl -fsSL https://bazel.build/bazel-release.pub.gpg | gpg --dearmor > bazel.gpg
sudo mv bazel.gpg /etc/apt/trusted.gpg.d/
echo "deb [arch=amd64] https://storage.googleapis.com/bazel-apt stable jdk1.8" | sudo tee /etc/apt/sources.list.d/bazel.list

sudo apt update && sudo apt install -y bazel
