---- MODULE LazyCacheFingerprint ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Adr,        \* abstract set of memory addresses
          Data,       \* abstract set of data values
          NumProcs,   \* number of processors
          InLen,      \* maximum length of each input buffer
          OutLen      \* maximum length of each output buffer

ASSUME /\ IsFiniteSet(Adr) /\ Adr # {}
       /\ IsFiniteSet(Data) /\ Data # {}
       /\ NumProcs \in Nat \ {0}
       /\ InLen \in Nat
       /\ OutLen \in Nat

Proc == 1..NumProcs

NoData == CHOOSE d : d \notin Data

Requests == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Data]

BoundedSeq(S, n) == UNION { [1..i -> S] : i \in 0..n }

-----------------------------------------------------------------------------
(* Recursive counting operators used to estimate the number of distinct states *)

RECURSIVE Pow(_, _)
Pow(b, e) == IF e = 0 THEN 1 ELSE b * Pow(b, e - 1)

\* Number of sequences over an alphabet of size k having length at most n
RECURSIVE NumSeqsUpTo(_, _)
NumSeqsUpTo(k, n) == IF n = 0 THEN 1 ELSE Pow(k, n) + NumSeqsUpTo(k, n - 1)

\* Number of functions from a domain of size d to a range of size r
NumFcns(d, r) == Pow(r, d)

NumMemStates    == NumFcns(Cardinality(Adr), Cardinality(Data))
NumCacheStates  == Pow(NumFcns(Cardinality(Adr), Cardinality(Data) + 1), NumProcs)
NumInputStates  == Pow(NumSeqsUpTo(Cardinality(Requests), InLen), NumProcs)
NumOutputStates == Pow(NumSeqsUpTo(Cardinality(Data), OutLen), NumProcs)

EstimatedStates == NumMemStates * NumCacheStates * NumInputStates * NumOutputStates

-----------------------------------------------------------------------------
VARIABLES mem, cache, input, output

vars == <<mem, cache, input, output>>

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ mem \in [Adr -> Data]
    /\ cache \in [Proc -> [Adr -> Data \cup {NoData}]]
    /\ input \in [Proc -> Seq(Requests)]
    /\ output \in [Proc -> Seq(Data)]

BoundsOK ==
    /\ \A p \in Proc : Len(input[p]) <= InLen
    /\ \A p \in Proc : Len(output[p]) <= OutLen

BufferTypeOK ==
    /\ input \in [Proc -> BoundedSeq(Requests, InLen)]
    /\ output \in [Proc -> BoundedSeq(Data, OutLen)]

CountOK == EstimatedStates \in Nat \ {0}

Inv == TypeOK /\ BoundsOK /\ BufferTypeOK /\ CountOK

-----------------------------------------------------------------------------
Init ==
    /\ mem \in [Adr -> Data]
    /\ cache = [p \in Proc |-> [a \in Adr |-> NoData]]
    /\ input = [p \in Proc |-> << >>]
    /\ output = [p \in Proc |-> << >>]

UpdateMem(a, d) ==
    /\ mem' = [mem EXCEPT ![a] = d]
    /\ UNCHANGED <<cache, input, output>>

UpdateCache(p, a, d) ==
    /\ cache' = [cache EXCEPT ![p][a] = d]
    /\ UNCHANGED <<mem, input, output>>

EnqueueInput(p, r) ==
    /\ Len(input[p]) < InLen
    /\ input' = [input EXCEPT ![p] = Append(@, r)]
    /\ UNCHANGED <<mem, cache, output>>

DequeueInput(p) ==
    /\ Len(input[p]) > 0
    /\ input' = [input EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<mem, cache, output>>

EnqueueOutput(p, d) ==
    /\ Len(output[p]) < OutLen
    /\ output' = [output EXCEPT ![p] = Append(@, d)]
    /\ UNCHANGED <<mem, cache, input>>

DequeueOutput(p) ==
    /\ Len(output[p]) > 0
    /\ output' = [output EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<mem, cache, input>>

Next ==
    \/ \E a \in Adr, d \in Data : UpdateMem(a, d)
    \/ \E p \in Proc, a \in Adr, d \in Data \cup {NoData} : UpdateCache(p, a, d)
    \/ \E p \in Proc, r \in Requests : EnqueueInput(p, r)
    \/ \E p \in Proc : DequeueInput(p)
    \/ \E p \in Proc, d \in Data : EnqueueOutput(p, d)
    \/ \E p \in Proc : DequeueOutput(p)

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Inv
=============================================================================