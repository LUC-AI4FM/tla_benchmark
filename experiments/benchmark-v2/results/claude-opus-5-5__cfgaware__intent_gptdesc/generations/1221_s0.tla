------------------------------ MODULE CacheMemory ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    N,          \* number of processors
    Addr,       \* finite set of memory addresses
    Data,       \* finite data domain
    InitData,   \* initial memory contents: a function Addr -> Data
    InLen,      \* maximum length of each processor's input queue
    OutLen,     \* maximum length of each processor's output queue
    ND          \* the explicit "unknown / not present" symbol for caches

ASSUME /\ N \in Nat \ {0}
       /\ IsFiniteSet(Addr)
       /\ IsFiniteSet(Data)
       /\ InitData \in [Addr -> Data]
       /\ InLen \in Nat
       /\ OutLen \in Nat
       /\ ND \notin Data

VARIABLES mem, cache, inq, outq

vars == <<mem, cache, inq, outq>>

Procs == 1 .. N

\* Ordinary read/write operations are address-data pairs. Special operations
\* carry a tag. All operations share one record shape so TLC can compare them.
OpKinds == {"rd", "wr", "tag"}
Ops     == [kind : OpKinds, addr : Addr, data : Data]

\* Responses are address-data pairs.
Resps   == [addr : Addr, data : Data]

CacheVal == Data \cup {ND}

\* Finite set of sequences over S of length at most n.
BSeq(S, n) == UNION { [1 .. k -> S] : k \in 0 .. n }

--------------------------------------------------------------------------------
Init ==
    /\ mem   = InitData
    /\ cache = [p \in Procs |-> [a \in Addr |-> ND]]
    /\ inq   = [p \in Procs |-> << >>]
    /\ outq  = [p \in Procs |-> << >>]

\* Arbitrary memory update. To keep the system coherent, every cache entry for
\* that address is either updated to the new value or invalidated to ND.
MemWrite(a, d) ==
    /\ mem' = [mem EXCEPT ![a] = d]
    /\ \E keep \in SUBSET Procs :
         cache' = [p \in Procs |->
                     [cache[p] EXCEPT ![a] = IF p \in keep THEN d ELSE ND]]
    /\ UNCHANGED <<inq, outq>>

\* Arbitrary processor-local cache update: fill with the current memory value,
\* or invalidate to ND.
CacheUpdate(p, a) ==
    /\ \E v \in {mem[a], ND} :
         cache' = [cache EXCEPT ![p][a] = v]
    /\ UNCHANGED <<mem, inq, outq>>

EnqIn(p, op) ==
    /\ Len(inq[p]) < InLen
    /\ inq' = [inq EXCEPT ![p] = Append(@, op)]
    /\ UNCHANGED <<mem, cache, outq>>

DeqIn(p) ==
    /\ inq[p] # << >>
    /\ inq' = [inq EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<mem, cache, outq>>

EnqOut(p, r) ==
    /\ Len(outq[p]) < OutLen
    /\ outq' = [outq EXCEPT ![p] = Append(@, r)]
    /\ UNCHANGED <<mem, cache, inq>>

DeqOut(p) ==
    /\ outq[p] # << >>
    /\ outq' = [outq EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<mem, cache, inq>>

Next ==
    \/ \E a \in Addr, d \in Data : MemWrite(a, d)
    \/ \E p \in Procs, a \in Addr : CacheUpdate(p, a)
    \/ \E p \in Procs, op \in Ops : EnqIn(p, op)
    \/ \E p \in Procs : DeqIn(p)
    \/ \E p \in Procs, r \in Resps : EnqOut(p, r)
    \/ \E p \in Procs : DeqOut(p)

Fairness ==
    \A p \in Procs : WF_vars(DeqIn(p)) /\ WF_vars(DeqOut(p))

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ mem   \in [Addr -> Data]
    /\ cache \in [Procs -> [Addr -> CacheVal]]
    /\ inq   \in [Procs -> BSeq(Ops, InLen)]
    /\ outq  \in [Procs -> BSeq(Resps, OutLen)]

QueueBounds ==
    \A p \in Procs : /\ Len(inq[p])  <= InLen
                     /\ Len(outq[p]) <= OutLen

Coherence ==
    \A p \in Procs, a \in Addr : cache[p][a] \in {mem[a], ND}

Inv == TypeOK /\ QueueBounds /\ Coherence

\* The reachable state space is contained in this finite set.
StateSpace ==
    [Addr -> Data] \X [Procs -> [Addr -> CacheVal]]
      \X [Procs -> BSeq(Ops, InLen)] \X [Procs -> BSeq(Resps, OutLen)]

Finite == <<mem, cache, inq, outq>> \in StateSpace

--------------------------------------------------------------------------------
\* Liveness / progress properties

\* Either the input queue is empty infinitely often, or it is dequeued
\* infinitely often. Enqueued operations are therefore eventually consumed.
InProgress ==
    \A p \in Procs :
        []<>(inq[p] = << >>) \/ []<><<DeqIn(p)>>_vars

OutProgress ==
    \A p \in Procs :
        []<>(outq[p] = << >>) \/ []<><<DeqOut(p)>>_vars

\* A nonempty queue eventually makes progress.
InLeadsTo ==
    \A p \in Procs : (inq[p] # << >>) ~> (inq[p] = << >> \/ ENABLED DeqIn(p))

OutLeadsTo ==
    \A p \in Procs : (outq[p] # << >>) ~> (outq[p] = << >> \/ ENABLED DeqOut(p))

Liveness == InProgress /\ OutProgress

THEOREM Spec => []Inv
THEOREM Spec => Liveness
================================================================================