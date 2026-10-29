---------------------------- MODULE LazyCacheFingerprintTest ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Data,      \* set of data values
          InitData,  \* initial data value of every memory location
          Addr,      \* set of addresses
          N,         \* number of processors
          InLen,     \* maximum length of an input queue
          OutLen,    \* maximum length of an output queue
          ND         \* "not present" sentinel for cache entries

ASSUME /\ N \in Nat \ {0}
       /\ InLen \in Nat
       /\ OutLen \in Nat
       /\ ND \notin Data

VARIABLES memory, cache, inq, outq

vars == <<memory, cache, inq, outq>>

Proc == 1..N

\* Operations are address-data pairs, optionally tagged
UntaggedOp == Addr \X Data
TaggedOp   == Addr \X Data \X {"tagged"}
Op         == UntaggedOp \cup TaggedOp

\* Responses are data-address pairs
Resp == Data \X Addr

\* Sequences over S of length at most L
BSeq(S, L) == UNION { [1..i -> S] : i \in 0..L }

\* Number of sequences of length at most L over a set of size k
RECURSIVE SeqCount(_, _)
SeqCount(k, L) == IF L = 0 THEN 1 ELSE k^L + SeqCount(k, L - 1)

NData == Cardinality(Data)
NAddr == Cardinality(Addr)

MemCount   == NData ^ NAddr
CacheCount == (NData + 1) ^ NAddr
InCount    == SeqCount(2 * NAddr * NData, InLen)
OutCount   == SeqCount(NAddr * NData, OutLen)

ExpectedStates == MemCount * ((CacheCount * InCount * OutCount) ^ N)

TypeOK ==
    /\ memory \in [Addr -> Data]
    /\ cache  \in [Proc -> [Addr -> Data \cup {ND}]]
    /\ inq    \in [Proc -> BSeq(Op, InLen)]
    /\ outq   \in [Proc -> BSeq(Resp, OutLen)]

Init ==
    /\ PrintT(<<"Expected number of distinct states:", ExpectedStates>>)
    /\ memory = [a \in Addr |-> InitData]
    /\ cache  = [p \in Proc |-> [a \in Addr |-> ND]]
    /\ inq    = [p \in Proc |-> << >>]
    /\ outq   = [p \in Proc |-> << >>]

UpdateMemory ==
    /\ \E a \in Addr, d \in Data :
          memory' = [memory EXCEPT ![a] = d]
    /\ UNCHANGED <<cache, inq, outq>>

UpdateCache(p) ==
    /\ \E a \in Addr, d \in Data \cup {ND} :
          cache' = [cache EXCEPT ![p][a] = d]
    /\ UNCHANGED <<memory, inq, outq>>

EnqIn(p) ==
    /\ Len(inq[p]) < InLen
    /\ \E op \in Op :
          inq' = [inq EXCEPT ![p] = Append(@, op)]
    /\ UNCHANGED <<memory, cache, outq>>

DeqIn(p) ==
    /\ inq[p] # << >>
    /\ inq' = [inq EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<memory, cache, outq>>

EnqOut(p) ==
    /\ Len(outq[p]) < OutLen
    /\ \E r \in Resp :
          outq' = [outq EXCEPT ![p] = Append(@, r)]
    /\ UNCHANGED <<memory, cache, inq>>

DeqOut(p) ==
    /\ outq[p] # << >>
    /\ outq' = [outq EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<memory, cache, inq>>

Next ==
    \/ UpdateMemory
    \/ \E p \in Proc :
          \/ UpdateCache(p)
          \/ EnqIn(p)
          \/ DeqIn(p)
          \/ EnqOut(p)
          \/ DeqOut(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

=============================================================================