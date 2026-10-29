------------------------------ MODULE LazyCacheFingerprint ------------------------------
(***************************************************************************)
(* Fingerprint test for a LazyCache-style system.  It models the possible *)
(* values of main memory, per-processor caches, and per-processor input   *)
(* and output buffers.  Recursive operators compute an estimate of the     *)
(* number of distinct states.  There are no temporal properties and no    *)
(* fairness conditions.  The spec checks only state-level type and bound  *)
(* invariants.                                                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Adr,      \* abstract set of addresses
          Val,      \* abstract set of data values
          N,        \* number of processors
          QLen      \* maximum length of input / output buffers

ASSUME /\ N \in Nat \ {0}
       /\ QLen \in Nat
       /\ Adr # {}
       /\ Val # {}
       /\ IsFiniteSet(Adr)
       /\ IsFiniteSet(Val)

VARIABLES memory,   \* memory[a] : value stored at address a
          cache,    \* cache[p][a] : cached value or NoVal
          inq,      \* inq[p]  : input buffer of processor p
          outq      \* outq[p] : output buffer of processor p

vars == <<memory, cache, inq, outq>>

Proc  == 1..N
NoVal == CHOOSE v : v \notin Val

Request == [type : {"Rd"}, adr : Adr]
             \cup [type : {"Wr"}, adr : Adr, val : Val]

Response == Val

\* All sequences over S of length at most n
BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

-----------------------------------------------------------------------------
(* Recursive counting operators used to estimate the number of states.    *)

RECURSIVE Pow(_, _)
Pow(b, e) == IF e = 0 THEN 1 ELSE b * Pow(b, e - 1)

\* Number of functions from a domain of size d into a range of size k
NumFcns(k, d) == Pow(k, d)

\* Number of sequences over a set of size k with length at most n
RECURSIVE NumSeqs(_, _)
NumSeqs(k, n) == IF n = 0 THEN 1 ELSE Pow(k, n) + NumSeqs(k, n - 1)

NumMemory    == NumFcns(Cardinality(Val), Cardinality(Adr))
NumCacheProc == NumFcns(Cardinality(Val) + 1, Cardinality(Adr))
NumInqProc   == NumSeqs(Cardinality(Request), QLen)
NumOutqProc  == NumSeqs(Cardinality(Response), QLen)

EstimatedStates ==
    NumMemory * Pow(NumCacheProc * NumInqProc * NumOutqProc, N)

-----------------------------------------------------------------------------
Init ==
    /\ memory \in [Adr -> Val]
    /\ cache  = [p \in Proc |-> [a \in Adr |-> NoVal]]
    /\ inq    = [p \in Proc |-> << >>]
    /\ outq   = [p \in Proc |-> << >>]

UpdateMemory ==
    \E a \in Adr, v \in Val :
        /\ memory' = [memory EXCEPT ![a] = v]
        /\ UNCHANGED <<cache, inq, outq>>

UpdateCache ==
    \E p \in Proc, a \in Adr, v \in Val \cup {NoVal} :
        /\ cache' = [cache EXCEPT ![p][a] = v]
        /\ UNCHANGED <<memory, inq, outq>>

EnqueueInput ==
    \E p \in Proc, r \in Request :
        /\ Len(inq[p]) < QLen
        /\ inq' = [inq EXCEPT ![p] = Append(@, r)]
        /\ UNCHANGED <<memory, cache, outq>>

DequeueInput ==
    \E p \in Proc :
        /\ inq[p] # << >>
        /\ inq' = [inq EXCEPT ![p] = Tail(@)]
        /\ UNCHANGED <<memory, cache, outq>>

EnqueueOutput ==
    \E p \in Proc, v \in Response :
        /\ Len(outq[p]) < QLen
        /\ outq' = [outq EXCEPT ![p] = Append(@, v)]
        /\ UNCHANGED <<memory, cache, inq>>

DequeueOutput ==
    \E p \in Proc :
        /\ outq[p] # << >>
        /\ outq' = [outq EXCEPT ![p] = Tail(@)]
        /\ UNCHANGED <<memory, cache, inq>>

Next ==
    \/ UpdateMemory
    \/ UpdateCache
    \/ EnqueueInput
    \/ DequeueInput
    \/ EnqueueOutput
    \/ DequeueOutput

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants                                                              *)

TypeOK ==
    /\ memory \in [Adr -> Val]
    /\ cache  \in [Proc -> [Adr -> Val \cup {NoVal}]]
    /\ inq    \in [Proc -> BoundedSeq(Request, QLen)]
    /\ outq   \in [Proc -> BoundedSeq(Response, QLen)]

BoundsOK ==
    \A p \in Proc :
        /\ Len(inq[p])  <= QLen
        /\ Len(outq[p]) <= QLen

EstimateOK == EstimatedStates \in Nat \ {0}

Inv == TypeOK /\ BoundsOK /\ EstimateOK

THEOREM Spec => [](TypeOK /\ BoundsOK)
=============================================================================