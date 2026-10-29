------------------------------- MODULE LazyCacheFingerprint -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Adr,          \* abstract set of memory addresses
    Val,          \* abstract set of data values
    NumProcs,     \* number of processors
    MaxInLen,     \* maximum length of each input buffer
    MaxOutLen     \* maximum length of each output buffer

ASSUME /\ NumProcs \in Nat \ {0}
       /\ MaxInLen \in Nat
       /\ MaxOutLen \in Nat
       /\ IsFiniteSet(Adr)
       /\ IsFiniteSet(Val)

VARIABLES memory, cache, inbuf, outbuf

vars == <<memory, cache, inbuf, outbuf>>

Proc == 1..NumProcs

NoVal == CHOOSE v : v \notin Val

CacheVal == Val \cup {NoVal}

ReqType == [type : {"Rd"}, adr : Adr] \cup [type : {"Wr"}, adr : Adr, val : Val]

BoundedSeq(S, n) == UNION { [1..i -> S] : i \in 0..n }

---------------------------------------------------------------------------------------------
\* Recursive operators used to count the possible values of the variables

RECURSIVE Power(_, _)
Power(b, e) == IF e = 0 THEN 1 ELSE b * Power(b, e - 1)

\* Number of sequences of length 0..n over a set with k elements
RECURSIVE SeqCount(_, _)
SeqCount(k, n) == IF n = 0 THEN 1 ELSE Power(k, n) + SeqCount(k, n - 1)

\* Number of functions from a domain of size d to a range of size r
FuncCount(d, r) == Power(r, d)

NumAdr == Cardinality(Adr)
NumVal == Cardinality(Val)
NumReq == NumAdr + NumAdr * NumVal

MemoryStates == FuncCount(NumAdr, NumVal)
CacheStates  == FuncCount(NumProcs, FuncCount(NumAdr, NumVal + 1))
InbufStates  == FuncCount(NumProcs, SeqCount(NumReq, MaxInLen))
OutbufStates == FuncCount(NumProcs, SeqCount(NumVal, MaxOutLen))

EstimatedStates == MemoryStates * CacheStates * InbufStates * OutbufStates

---------------------------------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ memory \in [Adr -> Val]
    /\ cache \in [Proc -> [Adr -> CacheVal]]
    /\ inbuf \in [Proc -> Seq(ReqType)]
    /\ outbuf \in [Proc -> Seq(Val)]

BoundsOK ==
    /\ \A p \in Proc : Len(inbuf[p]) <= MaxInLen
    /\ \A p \in Proc : Len(outbuf[p]) <= MaxOutLen

BoundedTypeOK ==
    /\ inbuf \in [Proc -> BoundedSeq(ReqType, MaxInLen)]
    /\ outbuf \in [Proc -> BoundedSeq(Val, MaxOutLen)]

EstimateOK == EstimatedStates \in Nat

---------------------------------------------------------------------------------------------

Init ==
    /\ memory \in [Adr -> Val]
    /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
    /\ inbuf = [p \in Proc |-> <<>>]
    /\ outbuf = [p \in Proc |-> <<>>]

MemUpdate(a, v) ==
    /\ memory' = [memory EXCEPT ![a] = v]
    /\ UNCHANGED <<cache, inbuf, outbuf>>

CacheUpdate(p, a, v) ==
    /\ cache' = [cache EXCEPT ![p][a] = v]
    /\ UNCHANGED <<memory, inbuf, outbuf>>

CacheEvict(p, a) ==
    /\ cache[p][a] # NoVal
    /\ cache' = [cache EXCEPT ![p][a] = NoVal]
    /\ UNCHANGED <<memory, inbuf, outbuf>>

InputEnqueue(p, r) ==
    /\ Len(inbuf[p]) < MaxInLen
    /\ inbuf' = [inbuf EXCEPT ![p] = Append(@, r)]
    /\ UNCHANGED <<memory, cache, outbuf>>

InputDequeue(p) ==
    /\ inbuf[p] # <<>>
    /\ inbuf' = [inbuf EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<memory, cache, outbuf>>

OutputEnqueue(p, v) ==
    /\ Len(outbuf[p]) < MaxOutLen
    /\ outbuf' = [outbuf EXCEPT ![p] = Append(@, v)]
    /\ UNCHANGED <<memory, cache, inbuf>>

OutputDequeue(p) ==
    /\ outbuf[p] # <<>>
    /\ outbuf' = [outbuf EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<memory, cache, inbuf>>

Next ==
    \/ \E a \in Adr, v \in Val : MemUpdate(a, v)
    \/ \E p \in Proc, a \in Adr, v \in Val : CacheUpdate(p, a, v)
    \/ \E p \in Proc, a \in Adr : CacheEvict(p, a)
    \/ \E p \in Proc, r \in ReqType : InputEnqueue(p, r)
    \/ \E p \in Proc : InputDequeue(p)
    \/ \E p \in Proc, v \in Val : OutputEnqueue(p, v)
    \/ \E p \in Proc : OutputDequeue(p)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------------------------

THEOREM Spec => [](TypeOK /\ BoundsOK /\ BoundedTypeOK)

=============================================================================================