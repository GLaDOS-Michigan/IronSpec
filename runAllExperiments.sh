#!/bin/bash

./cleanExperimentOutput.sh

./runMutationTestingExperiments.sh

./runASCExperiments.sh 

./gatherResults.sh 