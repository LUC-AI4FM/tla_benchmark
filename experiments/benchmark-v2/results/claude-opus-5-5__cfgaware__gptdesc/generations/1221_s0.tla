------------------------------- MODULE LazyCacheFP -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Data,      \* set of data values
          InitData,  \* initial value of every memory location
          Addr,      \* set of addresses
          N,         \* number of processors
          InLen,     \* maximum length of an input buffer
          OutLen,    \* maximum length of an output buffer
          ND         \* "no data" value (invalid cache entry)

ASSUME /\ InitData \in Data
       /\ ND \notin Data
       /\ N \in Nat \ {0}
       /\ InLen \in Nat
       /\ OutLen \in Nat

VARIABLES memory, cache, inQ, outQ

vars == <<memory, cache, inQ, outQ>>

Proc == 1..N

DataOrND == Data \cup {ND}

\* A request in an input buffer: an address and either a value to write or ND (a read)
Req == Addr \X DataOrND

BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

-----------------------------------------------------------------------------
(* Recursive operators that count the number of possible values, used to   *)
(* estimate the number of distinct states for the fingerprint test.        *)

RECURSIVE NumSeqs(_, _)
\* Number of sequences of length at most n over a set of size k
NumSeqs(k, n) == IF n = 0 THEN 1 ELSE k^n + NumSeqs(k, n - 1)

RECURSIVE Power(_, _)
Power(k, n) == IF n = 0 THEN 1 ELSE k * Power(k, n - 1)

\* Number of functions from a set of size m to a set of size k
NumFcns(m, k) == Power(k, m)

NumMemory == NumFcns(Cardinality(Addr), Cardinality(Data))
NumCache  == Power(NumFcns(Cardinality(Addr), Cardinality(DataOrND)), N)
NumInQ    == Power(NumSeqs(Cardinality(Req), InLen), N)
NumOutQ   == Power(NumSeqs(Cardinality(Data), OutLen), N)

NumStates == NumMemory * NumCache * NumInQ * NumOutQ

-----------------------------------------------------------------------------

Init == /\ memory = [a \in Addr |-> InitData]
        /\ cache  = [p \in Proc |-> [a \in Addr |-> ND]]
        /\ inQ    = [p \in Proc |-> << >>]
        /\ outQ   = [p \in Proc |-> << >>]

UpdateMemory ==
  /\ \E a \in Addr, d \in Data :
        memory' = [memory EXCEPT ![a] = d]
  /\ UNCHANGED <<cache, inQ, outQ>>

UpdateCache ==
  /\ \E p \in Proc, a \in Addr, d \in DataOrND :
        cache' = [cache EXCEPT ![p][a] = d]
  /\ UNCHANGED <<memory, inQ, outQ>>

EnqueueIn ==
  /\ \E p \in Proc, r \in Req :
        /\ Len(inQ[p]) < InLen
        /\ inQ' = [inQ EXCEPT ![p] = Append(@, r)]
  /\ UNCHANGED <<memory, cache, outQ>>

DequeueIn ==
  /\ \E p \in Proc :
        /\ inQ[p] # << >>
        /\ inQ' = [inQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<memory, cache, outQ>>

EnqueueOut ==
  /\ \E p \in Proc, d \in Data :
        /\ Len(outQ[p]) < OutLen
        /\ outQ' = [outQ EXCEPT ![p] = Append(@, d)]
  /\ UNCHANGED <<memory, cache, inQ>>

DequeueOut ==
  /\ \E p \in Proc :
        /\ outQ[p] # << >>
        /\ outQ' = [outQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<memory, cache, inQ>>

Next == \/ UpdateMemory
        \/ UpdateCache
        \/ EnqueueIn
        \/ DequeueIn
        \/ EnqueueOut
        \/ DequeueOut

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK ==
  /\ memory \in [Addr -> Data]
  /\ cache  \in [Proc -> [Addr -> DataOrND]]
  /\ inQ    \in [Proc -> Seq(Req)]
  /\ outQ   \in [Proc -> Seq(Data)]

BoundsOK ==
  /\ \A p \in Proc : Len(inQ[p]) <= InLen
  /\ \A p \in Proc : Len(outQ[p]) <= OutLen

Inv == /\ TypeOK
       /\ BoundsOK
       /\ inQ  \in [Proc -> BoundedSeq(Req, InLen)]
       /\ outQ \in [Proc -> BoundedSeq(Data, OutLen)]

=============================================================================