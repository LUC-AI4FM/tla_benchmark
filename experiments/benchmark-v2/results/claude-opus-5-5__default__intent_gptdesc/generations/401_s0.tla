------------------------- MODULE CacheCoherenceModel -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Adr,        \* finite set of memory addresses
    Val,        \* finite set of data values
    N,          \* number of processors
    InitMem,    \* initial shared-memory contents: a function Adr -> Val
    MaxIn,      \* maximum length of each processor's input (response) sequence
    MaxOut      \* maximum length of each processor's output (request) sequence

ASSUME ConstAssumptions ==
    /\ IsFiniteSet(Adr) /\ Adr # {}
    /\ IsFiniteSet(Val) /\ Val # {}
    /\ N \in Nat /\ N >= 1
    /\ InitMem \in [Adr -> Val]
    /\ MaxIn \in Nat
    /\ MaxOut \in Nat

Proc == 1..N

\* Abstract "unknown" marker, distinct from every data value
NoVal == CHOOSE v : v \notin Val

LocalVal == Val \cup {NoVal}

\* Requests / operations a processor may send
Request ==
    [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

\* Data responses a processor may receive
Response == [adr : Adr, val : Val]

\* Bounded sequences over a finite set (keeps the state space finite)
BSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

VARIABLES
    memory,   \* shared memory: Adr -> Val
    cache,    \* per-processor local view: Proc -> (Adr -> Val \cup {NoVal})
    inQ,      \* per-processor input sequence of responses
    outQ      \* per-processor output sequence of requests

vars == <<memory, cache, inQ, outQ>>

-----------------------------------------------------------------------------
\* Initialization

Init ==
    /\ memory = InitMem
    /\ cache \in [Proc -> [Adr -> LocalVal]]
    /\ \A p \in Proc : \A a \in Adr : cache[p][a] \in {InitMem[a], NoVal}
    /\ inQ  = [p \in Proc |-> << >>]
    /\ outQ = [p \in Proc |-> << >>]

-----------------------------------------------------------------------------
\* Atomic transitions

\* Nondeterministic shared-memory write; local views that would become stale
\* are marked unknown so that local-view consistency is preserved.
MemWrite(a, v) ==
    /\ memory' = [memory EXCEPT ![a] = v]
    /\ cache'  = [p \in Proc |->
                    [cache[p] EXCEPT ![a] = IF @ = v THEN v ELSE NoVal]]
    /\ UNCHANGED <<inQ, outQ>>

\* A processor updates its local view of an address with either the concrete
\* current memory value or the unknown marker.
LocalWrite(p, a) ==
    /\ \E v \in {memory[a], NoVal} :
           cache' = [cache EXCEPT ![p][a] = v]
    /\ UNCHANGED <<memory, inQ, outQ>>

\* A processor enqueues a request/operation to send.
EnqueueRequest(p, r) ==
    /\ Len(outQ[p]) < MaxOut
    /\ outQ' = [outQ EXCEPT ![p] = Append(@, r)]
    /\ UNCHANGED <<memory, cache, inQ>>

\* A sent request is removed once processed.
DequeueRequest(p) ==
    /\ outQ[p] # << >>
    /\ outQ' = [outQ EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<memory, cache, inQ>>

\* A data response is enqueued for a processor.
EnqueueResponse(p, r) ==
    /\ Len(inQ[p]) < MaxIn
    /\ inQ' = [inQ EXCEPT ![p] = Append(@, r)]
    /\ UNCHANGED <<memory, cache, outQ>>

\* A processor removes a processed response.
DequeueResponse(p) ==
    /\ inQ[p] # << >>
    /\ inQ' = [inQ EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<memory, cache, outQ>>

Next ==
    \/ \E a \in Adr, v \in Val : MemWrite(a, v)
    \/ \E p \in Proc, a \in Adr : LocalWrite(p, a)
    \/ \E p \in Proc, r \in Request : EnqueueRequest(p, r)
    \/ \E p \in Proc : DequeueRequest(p)
    \/ \E p \in Proc, r \in Response : EnqueueResponse(p, r)
    \/ \E p \in Proc : DequeueResponse(p)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ memory \in [Adr -> Val]
    /\ cache  \in [Proc -> [Adr -> LocalVal]]
    /\ inQ    \in [Proc -> Seq(Response)]
    /\ outQ   \in [Proc -> Seq(Request)]

BoundsOK ==
    /\ DOMAIN memory = Adr
    /\ DOMAIN cache = Proc
    /\ \A p \in Proc : DOMAIN cache[p] = Adr
    /\ DOMAIN inQ = Proc
    /\ DOMAIN outQ = Proc
    /\ \A p \in Proc : Len(inQ[p])  <= MaxIn
    /\ \A p \in Proc : Len(outQ[p]) <= MaxOut

\* Finite-state view: every reachable state lies in this finite set
FiniteStateOK ==
    /\ inQ  \in [Proc -> BSeq(Response, MaxIn)]
    /\ outQ \in [Proc -> BSeq(Request, MaxOut)]

\* Local-view consistency
Coherence ==
    \A p \in Proc : \A a \in Adr :
        cache[p][a] \in {memory[a], NoVal}

Inv == TypeOK /\ BoundsOK /\ FiniteStateOK /\ Coherence

THEOREM Spec => []Inv
=============================================================================