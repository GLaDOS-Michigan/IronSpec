#!/bin/sh

sudo wget https://packages.microsoft.com/config/ubuntu/20.04/packages-microsoft-prod.deb -O packages-microsoft-prod.deb
sudo dpkg -i packages-microsoft-prod.deb
sudo apt-get update
sudo apt-get install -y apt-transport-https dotnet-sdk-6.0 aspnetcore-runtime-6.0 dotnet-runtime-6.0
sudo apt-get install -y bazel-4.0.0
