"""The Python implementation of the gRPC dafny server client."""

from __future__ import print_function

import logging
import random
import sys

import grpc
import message_pb2
import message_pb2_grpc


def verify(stub):
    verification_request = message_pb2.VerificationRequest()
    with open(sys.argv[2], 'r') as f:
        verification_request.code = f.read()
    verification_request.arguments.append('/compile:0')
    verification_request.arguments.append('/rlimit:100000')
    verification_request.arguments.append('/allowGlobals')
    verification_request.arguments.append('/noNLarith')
    verification_request.arguments.append('/autoTriggers:1')
    verification_request.arguments.append('/verifyAllModules')
    verification_request.arguments.append('/exitAfterFirstError')
    response = stub.Verify(verification_request)
    print(f"Received response is {response.response}")

def run():
    with grpc.insecure_channel(sys.argv[1]) as channel:
        stub = message_pb2_grpc.DafnyServerStub(channel)
        verify(stub)


if __name__ == '__main__':
    if len(sys.argv) < 3:
        print (f'Usage: {sys.argv[0]} IP:PORT PATH')
        sys.exit(1)
    logging.basicConfig()
    run()
