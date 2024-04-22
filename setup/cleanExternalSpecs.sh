#!/bin/bash

echo "Removing external specs ..." 

rm -rf specs/awsESDK/aws-encryption-sdk-dafny/
rm -rf specs/daisy-nfsd/daisy-nfsd/
rm -rf specs/eth2/eth2.0-dafny/
rm -rf specs/qbft/qbft-formal-spec-and-verification/
rm -rf specs/dvt/distributed-validator-formal-specs-and-verification/
rm -rf specs/truesat/truesat/

echo "DONE" 
