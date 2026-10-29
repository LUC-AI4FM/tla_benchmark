---------------------------- MODULE LazyCacheFingerprintTest ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Adr,      \* abstract set of addresses
          Data,     \* abstract set of data values
          N,        \* number of processors
          InLen,    \* maximum length of each input buffer
          OutLen    \* maximum length of each output buffer

ASSUME /\ IsFiniteSet(Adr) /\ Adr # {}
       /\ IsFiniteSet(Data) /\ Data # {}
       /\ N \in Nat \ {0}
       /\ InLen \in Nat
       /\ OutLen \in Nat

VARIABLES mem, cache, inq, outq

vars == <<mem, cache, inq, outq>>

Proc == 1..N

NoData == CHOOSE v : v \notin Data

Requests == [type : {"Rd"}, adr : Adr] \cup [type : {"Wr"}, adr : Adr, val : Data]

BoundedSeq(S, n) == UNION { [1..m -> S] : m \in 0..n }

-----------------------------------------------------------------------------
(* Recursive counting operators used to estimate the number of distinct states *)

RECURSIVE Pow(_, _)
Pow(b, e) == IF e = 0 THEN 1 ELSE b * Pow(b, e - 1)

\* Number of sequences of length 0..n over an alphabet of size k
RECURSIVE NumSeqsUpTo(_, _)
NumSeqsUpTo(k, n) == IF n = 0 THEN 1 ELSE Pow(k, n) + NumSeqsUpTo(k, n - 1)

\* Number of functions from a domain of size d to a range of size r
NumFcns(d, r) == Pow(r, d)

NumAdr  == Cardinality(Adr)
NumData == Cardinality(Data)
NumReq  == NumAdr + NumAdr * NumData

NumMemStates   == NumFcns(NumAdr, NumData)
NumCacheStates == Pow(NumFcns(NumAdr, NumData + 1), N)
NumInStates    == Pow(NumSeqsUpTo(NumReq, InLen), N)
NumOutStates   == Pow(NumSeqsUpTo(NumData, OutLen), N)

EstimatedStates == NumMemStates * NumCacheStates * NumInStates * NumOutStates

-----------------------------------------------------------------------------
TypeOK ==
  /\ mem   \in [Adr -> Data]
  /\ cache \in [Proc -> [Adr -> Data \cup {NoData}]]
  /\ inq   \in [Proc -> Seq(Requests)]
  /\ outq  \in [Proc -> Seq(Data)]

BoundsOK ==
  /\ \A p \in Proc : Len(inq[p]) <= InLen
  /\ \A p \in Proc : Len(outq[p]) <= OutLen

BoundedTypeOK ==
  /\ mem   \in [Adr -> Data]
  /\ cache \in [Proc -> [Adr -> Data \cup {NoData}]]
  /\ inq   \in [Proc -> BoundedSeq(Requests, InLen)]
  /\ outq  \in [Proc -> BoundedSeq(Data, OutLen)]

EstimateOK == EstimatedStates \in Nat \ {0}

-----------------------------------------------------------------------------
Init ==
  /\ mem   \in [Adr -> Data]
  /\ cache = [p \in Proc |-> [a \in Adr |-> NoData]]
  /\ inq   = [p \in Proc |-> << >>]
  /\ outq  = [p \in Proc |-> << >>]

MemUpdate ==
  /\ \E a \in Adr, d \in Data : mem' = [mem EXCEPT ![a] = d]
  /\ UNCHANGED <<cache, inq, outq>>

CacheUpdate ==
  /\ \E p \in Proc, a \in Adr, d \in Data \cup {NoData} :
        cache' = [cache EXCEPT ![p][a] = d]
  /\ UNCHANGED <<mem, inq, outq>>

InputEnqueue ==
  /\ \E p \in Proc, r \in Requests :
        /\ Len(inq[p]) < InLen
        /\ inq' = [inq EXCEPT ![p] = Append(@, r)]
  /\ UNCHANGED <<mem, cache, outq>>

InputDequeue ==
  /\ \E p \in Proc :
        /\ inq[p] # << >>
        /\ inq' = [inq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, cache, outq>>

OutputEnqueue ==
  /\ \E p \in Proc, d \in Data :
        /\ Len(outq[p]) < OutLen
        /\ outq' = [outq EXCEPT ![p] = Append(@, d)]
  /\ UNCHANGED <<mem, cache, inq>>

OutputDequeue ==
  /\ \E p \in Proc :
        /\ outq[p] # << >>
        /\ outq' = [outq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, cache, inq>>

Next ==
  \/ MemUpdate
  \/ CacheUpdate
  \/ InputEnqueue
  \/ InputDequeue
  \/ OutputEnqueue
  \/ OutputDequeue

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ BoundsOK /\ BoundedTypeOK)
=============================================================================