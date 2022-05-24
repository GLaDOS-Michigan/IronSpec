"""The Python implementation of the gRPC dafny verifier server."""

from concurrent import futures
import logging
import tempfile
import time
import subprocess

import grpc
import verifier_pb2
import verifier_pb2_grpc

dafnyBinary='/BASE-DIRECTORY/dafny-holeEval/Binaries/Dafny'
# dafnyBinary='/Users/arminvak/BASE-DIRECTORY/dafny-holeEval/Binaries/Dafny'


class DafnyVerifierServiceServicer(verifier_pb2_grpc.DafnyVerifierServiceServicer):
    """Provides methods that implement functionality of dafny server."""

    def Verify(self, request, context):
        """Run Dafny and send the response back."""
        with tempfile.NamedTemporaryFile(suffix='.dfy') as tmp:
            with open(tmp.name, 'w') as f:
                f.write(request.code)
            cmdList = [dafnyBinary, tmp.name]
            cmdList.extend(request.arguments)
            print(f"Executing {cmdList}")
            process = subprocess.Popen(cmdList,
                     stdout=subprocess.PIPE, 
                    #  stderr=subprocess.PIPE
                     )
            stdout, stderr = process.communicate()
            response = verifier_pb2.VerificationResponse()
            response.response = stdout
            response.fileName = tmp.name
        return response

def serve():
    server = grpc.server(futures.ThreadPoolExecutor(max_workers=1))
    verifier_pb2_grpc.add_DafnyVerifierServiceServicer_to_server(
        DafnyVerifierServiceServicer(), server)
    server.add_insecure_port('[::]:50051')
    server.start()
    server.wait_for_termination()


if __name__ == '__main__':
    logging.basicConfig()
    serve()
