---- MODULE AlternatingBit ----
EXTENDS Naturals

CONSTANT Data

VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, rcvd

\* Correctness skeleton: abstract away the queues; only bits and data matter.
\* msgQ and ackQ are omitted in the skeleton; we keep only the bits.
====