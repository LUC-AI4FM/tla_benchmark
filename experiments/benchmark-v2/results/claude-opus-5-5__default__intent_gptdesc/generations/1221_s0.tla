------------------------------ MODULE CoherentCacheMemory ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    N,              \* number of processors
    Adr,            \* finite set of memory addresses
    Val,            \* finite data domain
    InitMem,        \* initial memory contents: a function Adr -> Val
    MaxInQLen,      \* maximum length of each processor's input queue
    MaxOutQLen      \* maximum length of each processor's output queue

ASSUME NAssump        == N \in Nat /\ N >= 1
ASSUME AdrAssump      == IsFiniteSet(Adr) /\ Adr # {}
ASSUME ValAssump      == IsFiniteSet(Val) /\ Val # {}
ASSUME InitMemAssump  == InitMem \in [Adr -> Val]
ASSUME QLenAssump     == MaxInQLen \in Nat /\ MaxOutQLen \in Nat

-----------------------------------------------------------------------------------------
Proc == 1..N

\* Explicit "unknown / not present" symbol for cache entries
Unknown == CHOOSE v : v \notin Val

CacheVal == Val \cup {Unknown}

\* Special tags for tagged (non read/write) operations
SpecialTags == {"Fence", "Flush"}

\* Operations: ordinary read/write address-data pairs, or special tagged operations
RWOps      == [op : {"Rd", "Wr"}, adr : Adr, val : Val]
TaggedOps  == [op : {"Special"}, tag : SpecialTags]
Ops        == RWOps \cup TaggedOps

\* Responses: address-data pairs
Resps == [adr : Adr, val : Val]

\* Bounded sequences over a set S with length at most n
BSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

-----------------------------------------------------------------------------------------
VARIABLES
    memory,   \* memory[a] : current value at address a
    cache,    \* cache[p][a] : value cached by processor p for a, or Unknown
    inQ,      \* inQ[p] : input queue of operations of processor p
    outQ      \* outQ[p] : output queue of responses of processor p

vars == <<memory, cache, inQ, outQ>>

-----------------------------------------------------------------------------------------
Init ==
    /\ memory = InitMem
    /\ cache  = [p \in Proc |-> [a \in Adr |-> Unknown]]
    /\ inQ    = [p \in Proc |-> << >>]
    /\ outQ   = [p \in Proc |-> << >>]

\* Arbitrary memory update at any address. To keep caches coherent, every
\* processor's entry for that address is either refreshed to the new value
\* or invalidated (set to Unknown).
MemUpdate(a, d, S) ==
    /\ memory' = [memory EXCEPT ![a] = d]
    /\ cache'  = [p \in Proc |->
                    [cache[p] EXCEPT ![a] = IF p \in S THEN d ELSE Unknown]]
    /\ UNCHANGED <<inQ, outQ>>

\* Arbitrary processor-local cache update: set an entry to the current memory
\* value or to Unknown.
CacheUpdate(p, a, v) ==
    /\ v \in {memory[a], Unknown}
    /\ cache' = [cache EXCEPT ![p][a] = v]
    /\ UNCHANGED <<memory, inQ, outQ>>

EnqIn(p, o) ==
    /\ Len(inQ[p]) < MaxInQLen
    /\ inQ' = [inQ EXCEPT ![p] = Append(@, o)]
    /\ UNCHANGED <<memory, cache, outQ>>

DeqIn(p) ==
    /\ inQ[p] # << >>
    /\ inQ' = [inQ EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<memory, cache, outQ>>

EnqOut(p, r) ==
    /\ Len(outQ[p]) < MaxOutQLen
    /\ outQ' = [outQ EXCEPT ![p] = Append(@, r)]
    /\ UNCHANGED <<memory, cache, inQ>>

DeqOut(p) ==
    /\ outQ[p] # << >>
    /\ outQ' = [outQ EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<memory, cache, inQ>>

Next ==
    \/ \E a \in Adr, d \in Val, S \in SUBSET Proc : MemUpdate(a, d, S)
    \/ \E p \in Proc, a \in Adr, v \in CacheVal : CacheUpdate(p, a, v)
    \/ \E p \in Proc, o \in Ops   : EnqIn(p, o)
    \/ \E p \in Proc              : DeqIn(p)
    \/ \E p \in Proc, r \in Resps : EnqOut(p, r)
    \/ \E p \in Proc              : DeqOut(p)

Fairness ==
    /\ \A p \in Proc : WF_vars(DeqIn(p))
    /\ \A p \in Proc : WF_vars(DeqOut(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------------
\* Safety: every variable stays within its declared (finite) domain
TypeOK ==
    /\ memory \in [Adr -> Val]
    /\ cache  \in [Proc -> [Adr -> CacheVal]]
    /\ inQ    \in [Proc -> BSeq(Ops, MaxInQLen)]
    /\ outQ   \in [Proc -> BSeq(Resps, MaxOutQLen)]

\* Safety: queue lengths never exceed their maxima
QueueBounds ==
    \A p \in Proc : /\ Len(inQ[p])  <= MaxInQLen
                    /\ Len(outQ[p]) <= MaxOutQLen

\* Safety: caches hold either the current memory value or Unknown
CacheCoherence ==
    \A p \in Proc, a \in Adr : cache[p][a] \in {memory[a], Unknown}

\* Finiteness of the state space: all declared domains are finite
FiniteDomains ==
    /\ IsFiniteSet(Proc)
    /\ IsFiniteSet(CacheVal)
    /\ IsFiniteSet(Ops)
    /\ IsFiniteSet(Resps)

Invariants == TypeOK /\ QueueBounds /\ CacheCoherence

-----------------------------------------------------------------------------------------
\* Liveness / progress: enqueued items can eventually be dequeued.
\* Whenever a queue is non-empty, it eventually shrinks or a dequeue occurs.
InQProgress ==
    \A p \in Proc :
        []<>(inQ[p] = << >>) \/ []<><<DeqIn(p)>>_vars

OutQProgress ==
    \A p \in Proc :
        []<>(outQ[p] = << >>) \/ []<><<DeqOut(p)>>_vars

InQEventuallyDequeued ==
    \A p \in Proc : (inQ[p] # << >>) ~> (<<DeqIn(p)>>_vars \/ inQ[p] = << >>)

Liveness == InQProgress /\ OutQProgress

-----------------------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => Liveness
=========================================================================================