# -*- coding: utf-8 -*-
# Generated by the protocol buffer compiler.  DO NOT EDIT!
# source: verifier.proto
"""Generated protocol buffer code."""
from google.protobuf import descriptor as _descriptor
from google.protobuf import descriptor_pool as _descriptor_pool
from google.protobuf import message as _message
from google.protobuf import reflection as _reflection
from google.protobuf import symbol_database as _symbol_database
# @@protoc_insertion_point(imports)

_sym_db = _symbol_database.Default()




DESCRIPTOR = _descriptor_pool.Default().AddSerializedFile(b'\n\x0everifier.proto\x12\x13\x44\x61\x66nyExecutorServer\"6\n\x13VerificationRequest\x12\x0c\n\x04\x63ode\x18\x01 \x01(\t\x12\x11\n\targuments\x18\x02 \x03(\t\"d\n\x14VerificationResponse\x12\x10\n\x08response\x18\x01 \x01(\t\x12\x10\n\x08\x66ileName\x18\x02 \x01(\t\x12\x11\n\tstartTime\x18\x03 \x01(\x02\x12\x15\n\rexecutionTime\x18\x04 \x01(\x02\x32w\n\x14\x44\x61\x66nyVerifierService\x12_\n\x06Verify\x12(.DafnyExecutorServer.VerificationRequest\x1a).DafnyExecutorServer.VerificationResponse\"\x00\x42\x12\xaa\x02\x0fMicrosoft.Dafnyb\x06proto3')



_VERIFICATIONREQUEST = DESCRIPTOR.message_types_by_name['VerificationRequest']
_VERIFICATIONRESPONSE = DESCRIPTOR.message_types_by_name['VerificationResponse']
VerificationRequest = _reflection.GeneratedProtocolMessageType('VerificationRequest', (_message.Message,), {
  'DESCRIPTOR' : _VERIFICATIONREQUEST,
  '__module__' : 'verifier_pb2'
  # @@protoc_insertion_point(class_scope:DafnyExecutorServer.VerificationRequest)
  })
_sym_db.RegisterMessage(VerificationRequest)

VerificationResponse = _reflection.GeneratedProtocolMessageType('VerificationResponse', (_message.Message,), {
  'DESCRIPTOR' : _VERIFICATIONRESPONSE,
  '__module__' : 'verifier_pb2'
  # @@protoc_insertion_point(class_scope:DafnyExecutorServer.VerificationResponse)
  })
_sym_db.RegisterMessage(VerificationResponse)

_DAFNYVERIFIERSERVICE = DESCRIPTOR.services_by_name['DafnyVerifierService']
if _descriptor._USE_C_DESCRIPTORS == False:

  DESCRIPTOR._options = None
  DESCRIPTOR._serialized_options = b'\252\002\017Microsoft.Dafny'
  _VERIFICATIONREQUEST._serialized_start=39
  _VERIFICATIONREQUEST._serialized_end=93
  _VERIFICATIONRESPONSE._serialized_start=95
  _VERIFICATIONRESPONSE._serialized_end=195
  _DAFNYVERIFIERSERVICE._serialized_start=197
  _DAFNYVERIFIERSERVICE._serialized_end=316
# @@protoc_insertion_point(module_scope)