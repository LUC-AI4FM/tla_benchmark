------------------------------ MODULE LazyCacheFingerprint ------------------------------
(***************************************************************************)
(* Fingerprint test for the state space of a LazyCache system.             *)
(* Models the possible values of memory, per-processor caches, and         *)
(* per-processor input and output buffers. Recursive operators count the   *)
(* number of possible sequences and function values to estimate the        *)
(* number of distinct states.                                              *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Adr,        \* abstract set of addresses
          Val,        \* abstract set of data values
          NoVal,      \* marker for an invalid (empty) cache entry
          NumProcs,   \* number of processors
          InLen,      \* maximum length of each input buffer
          OutLen      \* maximum length of each output buffer

ASSUME /\ IsFiniteSet(Adr) /\ Adr # {}
       /\ IsFiniteSet(Val) /\ Val # {}
       /\ NoVal \notin Val
       /\ NumProcs \in Nat \ {0}
       /\ InLen \in Nat
       /\ OutLen \in Nat

VARIABLES memory, cache, inBuf, outBuf

vars == <<memory, cache, inBuf, outBuf>>

Proc == 1..NumProcs

CacheVal == Val \cup {NoVal}

(* Requests that may appear in an input buffer *)
Req == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

(* Sequences over S of length at most n *)
BSeq(S, n) == UNION { [1..i -> S] : i \in 0..n }

-----------------------------------------------------------------------------
(* Recursive counting operators *)

RECURSIVE Pow(_, _)
Pow(b, e) == IF e = 0 THEN 1 ELSE b * Pow(b, e - 1)

(* Number of sequences of length 0..n over an alphabet of size k *)
RECURSIVE NumSeqs(_, _)
NumSeqs(k, n) == IF n = 0 THEN 1 ELSE Pow(k, n) + NumSeqs(k, n - 1)

(* Number of functions from a domain of size d to a range of size r *)
NumFcns(d, r) == Pow(r, d)

NumReqs == Cardinality(Adr) + Cardinality(Adr) * Cardinality(Val)

NumMemory == NumFcns(Cardinality(Adr), Cardinality(Val))
NumCache  == Pow(NumFcns(Cardinality(Adr), Cardinality(CacheVal)), NumProcs)
NumInBuf  == Pow(NumSeqs(NumReqs, InLen), NumProcs)
NumOutBuf == Pow(NumSeqs(Cardinality(Val), OutLen), NumProcs)

NumStates == NumMemory * NumCache * NumInBuf * NumOutBuf

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ memory \in [Adr -> Val]
    /\ cache  \in [Proc -> [Adr -> CacheVal]]
    /\ inBuf  \in [Proc -> Seq(Req)]
    /\ outBuf \in [Proc -> Seq(Val)]

BoundsOK ==
    /\ \A p \in Proc : Len(inBuf[p]) \in 0..InLen
    /\ \A p \in Proc : Len(outBuf[p]) \in 0..OutLen

Inv == TypeOK /\ BoundsOK

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ memory \in [Adr -> Val]
    /\ cache  = [p \in Proc |-> [a \in Adr |-> NoVal]]
    /\ inBuf  = [p \in Proc |-> << >>]
    /\ outBuf = [p \in Proc |-> << >>]

-----------------------------------------------------------------------------
(* Actions *)

UpdateMemory ==
    /\ \E a \in Adr, v \in Val : memory' = [memory EXCEPT ![a] = v]
    /\ UNCHANGED <<cache, inBuf, outBuf>>

UpdateCache ==
    /\ \E p \in Proc, a \in Adr, v \in CacheVal :
          cache' = [cache EXCEPT ![p][a] = v]
    /\ UNCHANGED <<memory, inBuf, outBuf>>

EnqueueInput ==
    /\ \E p \in Proc, r \in Req :
          /\ Len(inBuf[p]) < InLen
          /\ inBuf' = [inBuf EXCEPT ![p] = Append(@, r)]
    /\ UNCHANGED <<memory, cache, outBuf>>

DequeueInput ==
    /\ \E p \in Proc :
          /\ inBuf[p] # << >>
          /\ inBuf' = [inBuf EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<memory, cache, outBuf>>

EnqueueOutput ==
    /\ \E p \in Proc, v \in Val :
          /\ Len(outBuf[p]) < OutLen
          /\ outBuf' = [outBuf EXCEPT ![p] = Append(@, v)]
    /\ UNCHANGED <<memory, cache, inBuf>>

DequeueOutput ==
    /\ \E p \in Proc :
          /\ outBuf[p] # << >>
          /\ outBuf' = [outBuf EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<memory, cache, inBuf>>

Next ==
    \/ UpdateMemory
    \/ UpdateCache
    \/ EnqueueInput
    \/ DequeueInput
    \/ EnqueueOutput
    \/ DequeueOutput

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
=============================================================================