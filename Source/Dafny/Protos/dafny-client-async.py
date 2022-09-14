"""The Python implementation of the gRPC dafny server client."""

from __future__ import print_function

from pathlib import Path
import logging
import threading
import time
import sys
import numpy as np
from google.protobuf import text_format

import grpc
import verifier_pb2
import verifier_pb2_grpc

start_time = time.time()

def verify(stub, iter):
    verification_request = verifier_pb2.VerificationRequest()
    with open(sys.argv[3], 'r') as f:
        verification_request.code = f.read()
    verification_request.arguments.append('/compile:0')
    verification_request.arguments.append('/rlimit:100000')
    verification_request.arguments.append('/allowGlobals')
    verification_request.arguments.append('/noNLarith')
    verification_request.arguments.append('/autoTriggers:1')
    verification_request.arguments.append('/verifyAllModules')
    verification_request.arguments.append('/exitAfterFirstError')
    response = stub.Verify(verification_request, timeout=1000000000)
    print(f"{int(time.time() - start_time)}: Received response #{iter} with startTime={response.startTime} executionTime={response.executionTime}")
    with open(f"{sys.argv[4]}/output_{iter}.txt", "w") as f:
        f.write(text_format.MessageToString(response))

def run():
    with grpc.insecure_channel(sys.argv[1], 
    #   options=[('grpc.max_concurrent_streams', 10)]
    ) as channel:
        stub = verifier_pb2_grpc.DafnyVerifierServiceStub(channel)
        threads = []
        for i in np.arange(int(sys.argv[2])):
            t = threading.Thread(target=verify, args = [stub, i])
            threads.append(t)
            t.start()
        for i in np.arange(int(sys.argv[2])):
            threads[i].join()
        print(f"{int(time.time() - start_time)}: Finish executing")


if __name__ == '__main__':
    if len(sys.argv) < 5:
        print (f'Usage: {sys.argv[0]} IP:PORT CNT PATH OUTPUT_DIR')
        sys.exit(1)
    logging.basicConfig()
    Path(sys.argv[4]).mkdir(parents=True, exist_ok=True)        
    run()
