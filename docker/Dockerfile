FROM ubuntu:20.04

ARG BUILD_DEPS="openjdk-13-jdk ca-certificates gnupg2 git apt-utils wget time make unzip graphviz apt-transport-https python3-pip clang libc++-dev"
ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
  && apt-get install -y ${BUILD_DEPS} --no-install-recommends
RUN python3 -m pip install grpcio grpcio-tools
RUN apt-key adv --keyserver keyserver.ubuntu.com --recv-keys A6A19B38D3D831EF
RUN wget https://packages.microsoft.com/config/ubuntu/20.04/packages-microsoft-prod.deb -O /tmp/packages-microsoft-prod.deb \
  && dpkg -i /tmp/packages-microsoft-prod.deb \
  && rm /tmp/packages-microsoft-prod.deb

RUN apt-get update \
  && apt-get install -y apt-transport-https dotnet-sdk-6.0 aspnetcore-runtime-6.0 dotnet-runtime-6.0

# install customized boogie
RUN mkdir BASE-DIRECTORY
RUN git clone https://github.com/arminvakil/boogie-1.git /BASE-DIRECTORY/boogie/
#COPY boogie/ BASE-DIRECTORY/boogie/

RUN cd BASE-DIRECTORY/boogie \
  && dotnet build Source/Boogie.sln\
  && cd ../../

ARG CLONE_DAFNY=false
RUN git clone https://github.com/GLaDOS-Michigan/dafny-holeEval.git /BASE-DIRECTORY/dafny-holeEval/
# COPY dafny-holeEval/ BASE-DIRECTORY/dafny-holeEval/

RUN cd BASE-DIRECTORY/dafny-holeEval \
  && dotnet build Source/Dafny.sln \
  && make z3-ubuntu \
  && cd ../../

CMD ["python3", "/BASE-DIRECTORY/dafny-holeEval/dafny-server/dafny-server.py"]
