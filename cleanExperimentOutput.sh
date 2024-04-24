#!/bin/bash

echo -e "Running IronSpec Experiments \n"

# clean up output from any previous experiments
if [ -d "$(pwd)/experimentOutput" ]; then rm -Rf $(pwd)/experimentOutput; fi

mkdir experimentOutput

# clean up any remaining output logs
if [ -d "$(pwd)/outputLogs" ]; then rm -Rf $(pwd)/outputLogs/* ; fi