------------------------- MODULE WriteThroughCache -------------------------
(***************************************************************************)
(* Write-through cache system: several processors with private caches     *)
(* share one memory. Every memory request goes through a bounded FIFO      *)
(* queue that a memory coordinator services in order.                      *)
(*                                                                         *)
(*  - A read either hits in the private cache, or misses and enqueues a    *)
(*    memory-read request. The coordinator serves that request from        *)
(*    memory, and the response is later delivered to the processor.       *)
(*  - A write updates the private cache and enqueues a memory-write        *)
(*    request (write-through). If the queue is full, the write blocks.     *)
(*  - When a write is applied to memory, the coordinator invalidates the   *)
(*    copies held by other caches. It also marks any undelivered read      *)
(*    responses for that address as stale (snooping invalidation).        *)
(*  - Cache capacity is abstract: at most CacheSize lines per cache, with  *)
(*    replacement and spontaneous eviction.                                *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,       \* set of processors
          Addr,       \* abstract set of memory addresses
          Val,        \* abstract set of data values
          QLen,       \* capacity of the memory-request queue
          CacheSize,  \* number of lines in each private cache
          MaxOps      \* bound on operations issued per processor (finite model)

ASSUME /\ QLen \in Nat \ {0}
       /\ CacheSize \in Nat \ {0}
       /\ MaxOps \in Nat
       /\ Proc # {} /\ Addr # {} /\ Val # {}

NoVal   == CHOOSE v : v \notin Val
InitVal == CHOOSE v \in Val : TRUE
AnyAddr == CHOOSE a \in Addr : TRUE
NoResp  == [ready |-> FALSE, val |-> NoVal, valid |-> FALSE]

ReqId   == Proc \X (1..MaxOps)
Request == [id : ReqId, type : {"read", "write"}, proc : Proc,
            addr : Addr, val : Val \cup {NoVal}]

VARIABLES memory,   \* shared memory: Addr -> Val
          cache,    \* cache[p][a] \in Val \cup {NoVal}
          queue,    \* bounded FIFO of memory requests
          pstate,   \* processor state
          preq,     \* current operation of each processor
          resp,     \* response channel coordinator -> processor
          opCnt,    \* number of operations issued by each processor
          applied,  \* op number of the last write of p applied to memory
          enqHist,  \* ghost: every request ever enqueued, in order
          deqHist   \* ghost: every request ever dequeued, in order

vars == <<memory, cache, queue, pstate, preq, resp, opCnt, applied,
          enqHist, deqHist>>

-----------------------------------------------------------------------------
Cached(c) == {x \in Addr : c[x] # NoVal}

\* Insert a line into a cache. If the cache is full, an arbitrary victim
\* line is replaced first.
CacheInsert(c, a, v) ==
    IF c[a] # NoVal \/ Cardinality(Cached(c)) < CacheSize
       THEN [c EXCEPT ![a] = v]
       ELSE LET victim == CHOOSE x \in Cached(c) : TRUE
            IN  [c EXCEPT ![victim] = NoVal, ![a] = v]

QueueHasSpace == Len(queue) < QLen

-----------------------------------------------------------------------------
TypeOK ==
    /\ memory \in [Addr -> Val]
    /\ cache \in [Proc -> [Addr -> Val \cup {NoVal}]]
    /\ queue \in Seq(Request)
    /\ pstate \in [Proc -> {"idle", "readReq", "writeReq", "waitResp"}]
    /\ preq \in [Proc -> [addr : Addr, val : Val \cup {NoVal}]]
    /\ resp \in [Proc -> [ready : BOOLEAN, val : Val \cup {NoVal},
                          valid : BOOLEAN]]
    /\ opCnt \in [Proc -> 0..MaxOps]
    /\ applied \in [Proc -> 0..MaxOps]
    /\ enqHist \in Seq(Request)
    /\ deqHist \in Seq(Request)

Init ==
    /\ memory  = [a \in Addr |-> InitVal]
    /\ cache   = [p \in Proc |-> [a \in Addr |-> NoVal]]
    /\ queue   = << >>
    /\ pstate  = [p \in Proc |-> "idle"]
    /\ preq    = [p \in Proc |-> [addr |-> AnyAddr, val |-> NoVal]]
    /\ resp    = [p \in Proc |-> NoResp]
    /\ opCnt   = [p \in Proc |-> 0]
    /\ applied = [p \in Proc |-> 0]
    /\ enqHist = << >>
    /\ deqHist = << >>

-----------------------------------------------------------------------------
(* Processor actions *)

IssueRead(p, a) ==
    /\ pstate[p] = "idle"
    /\ opCnt[p] < MaxOps
    /\ pstate' = [pstate EXCEPT ![p] = "readReq"]
    /\ preq'   = [preq EXCEPT ![p] = [addr |-> a, val |-> NoVal]]
    /\ opCnt'  = [opCnt EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<memory, cache, queue, resp, applied, enqHist, deqHist>>

IssueWrite(p, a, v) ==
    /\ pstate[p] = "idle"
    /\ opCnt[p] < MaxOps
    /\ pstate' = [pstate EXCEPT ![p] = "writeReq"]
    /\ preq'   = [preq EXCEPT ![p] = [addr |-> a, val |-> v]]
    /\ opCnt'  = [opCnt EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<memory, cache, queue, resp, applied, enqHist, deqHist>>

\* The read hits and completes locally.
ReadHit(p) ==
    /\ pstate[p] = "readReq"
    /\ cache[p][preq[p].addr] # NoVal
    /\ pstate' = [pstate EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<memory, cache, queue, preq, resp, opCnt, applied,
                   enqHist, deqHist>>

\* The read misses and a memory-read request is enqueued.
ReadMiss(p) ==
    /\ pstate[p] = "readReq"
    /\ cache[p][preq[p].addr] = NoVal
    /\ QueueHasSpace
    /\ LET r == [id |-> <<p, opCnt[p]>>, type |-> "read", proc |-> p,
                 addr |-> preq[p].addr, val |-> NoVal]
       IN  /\ queue'   = Append(queue, r)
           /\ enqHist' = Append(enqHist, r)
    /\ pstate' = [pstate EXCEPT ![p] = "waitResp"]
    /\ UNCHANGED <<memory, cache, preq, resp, opCnt, applied, deqHist>>

\* Write-through: update the cache and enqueue a memory-write request.
\* This action blocks while the queue is full.
EnqueueWrite(p) ==
    /\ pstate[p] = "writeReq"
    /\ QueueHasSpace
    /\ LET a == preq[p].addr
           v == preq[p].val
           r == [id |-> <<p, opCnt[p]>>, type |-> "write", proc |-> p,
                 addr |-> a, val |-> v]
       IN  /\ cache'   = [cache EXCEPT ![p] = CacheInsert(@, a, v)]
           /\ queue'   = Append(queue, r)
           /\ enqHist' = Append(enqHist, r)
    /\ pstate' = [pstate EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<memory, preq, resp, opCnt, applied, deqHist>>

\* Deliver a read response to the waiting processor. The value is
\* installed in the cache only if it has not been invalidated since then.
Deliver(p) ==
    /\ pstate[p] = "waitResp"
    /\ resp[p].ready
    /\ cache' = IF resp[p].valid
                   THEN [cache EXCEPT ![p] =
                           CacheInsert(@, preq[p].addr, resp[p].val)]
                   ELSE cache
    /\ resp'   = [resp EXCEPT ![p] = NoResp]
    /\ pstate' = [pstate EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<memory, queue, preq, opCnt, applied, enqHist, deqHist>>

\* Spontaneous eviction, an abstract replacement policy.
Evict(p, a) ==
    /\ cache[p][a] # NoVal
    /\ cache' = [cache EXCEPT ![p][a] = NoVal]
    /\ UNCHANGED <<memory, queue, pstate, preq, resp, opCnt, applied,
                   enqHist, deqHist>>

-----------------------------------------------------------------------------
(* Memory coordinator actions: FIFO servicing of the queue *)

\* Serve a read request directly from memory.
ServeRead ==
    /\ queue # << >>
    /\ Head(queue).type = "read"
    /\ LET r == Head(queue)
       IN  /\ resp' = [resp EXCEPT ![r.proc] =
                         [ready |-> TRUE, val |-> memory[r.addr],
                          valid |-> TRUE]]
           /\ deqHist' = Append(deqHist, r)
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<memory, cache, pstate, preq, opCnt, applied, enqHist>>

\* Apply a write request to memory. Other caches' copies are invalidated,
\* and undelivered responses for the same address are marked stale.
ApplyWrite ==
    /\ queue # << >>
    /\ Head(queue).type = "write"
    /\ LET r == Head(queue)
       IN  /\ memory'  = [memory EXCEPT ![r.addr] = r.val]
           /\ cache'   = [q \in Proc |->
                            IF q # r.proc
                               THEN [cache[q] EXCEPT ![r.addr] = NoVal]
                               ELSE cache[q]]
           /\ resp'    = [q \in Proc |->
                            IF q # r.proc /\ resp[q].ready
                                          /\ preq[q].addr = r.addr
                               THEN [resp[q] EXCEPT !.valid = FALSE]
                               ELSE resp[q]]
           /\ applied' = [applied EXCEPT ![r.proc] = r.id[2]]
           /\ deqHist' = Append(deqHist, r)
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<pstate, preq, opCnt, enqHist>>

-----------------------------------------------------------------------------
ProcStep(p) == ReadHit(p) \/ ReadMiss(p) \/ EnqueueWrite(p)
MemStep     == ServeRead \/ ApplyWrite

\* Stuttering step once all work is finished (avoids spurious deadlock).
Terminated ==
    /\ \A p \in Proc : pstate[p] = "idle" /\ opCnt[p] = MaxOps
    /\ queue = << >>
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Proc, a \in Addr : IssueRead(p, a)
    \/ \E p \in Proc, a \in Addr, v \in Val : IssueWrite(p, a, v)
    \/ \E p \in Proc : ProcStep(p)
    \/ \E p \in Proc : Deliver(p)
    \/ \E p \in Proc, a \in Addr : Evict(p, a)
    \/ MemStep
    \/ Terminated

Fairness ==
    /\ WF_vars(ServeRead)
    /\ WF_vars(ApplyWrite)
    /\ \A p \in Proc : SF_vars(ProcStep(p))   \* enqueue may be enabled only intermittently
    /\ \A p \in Proc : WF_vars(Deliver(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

PendingWrites(p, a) ==
    {i \in DOMAIN queue : /\ queue[i].type = "write"
                          /\ queue[i].proc = p
                          /\ queue[i].addr = a}

MaxIdx(S) == CHOOSE i \in S : \A j \in S : j <= i

\* Cache coherence: a cached value is either the latest write of this
\* processor that has not yet reached memory, or else the current memory
\* value, which is the most recent write that is visible.
CacheCoherence ==
    \A p \in Proc, a \in Addr :
        cache[p][a] # NoVal =>
            IF PendingWrites(p, a) = {}
               THEN cache[p][a] = memory[a]
               ELSE cache[p][a] = queue[MaxIdx(PendingWrites(p, a))].val

\* A response that is still valid reflects the current memory contents.
ResponseCoherence ==
    \A p \in Proc :
        (resp[p].ready /\ resp[p].valid) => resp[p].val = memory[preq[p].addr]

\* Memory consistency: each processor's requests are kept in program order
\* in the queue, and pending writes are newer than every applied write.
ProgramOrder ==
    /\ \A i, j \in DOMAIN queue :
          (i < j /\ queue[i].proc = queue[j].proc) =>
              queue[i].id[2] < queue[j].id[2]
    /\ \A i \in DOMAIN queue :
          queue[i].type = "write" => queue[i].id[2] > applied[queue[i].proc]

\* FIFO order with no request lost or duplicated.
FIFOOrder == enqHist = deqHist \o queue

NoDuplication ==
    \A i, j \in DOMAIN enqHist : i # j => enqHist[i].id # enqHist[j].id

\* Bounds: the queue never exceeds its capacity.
QueueBound == Len(queue) <= QLen

\* At most one outstanding operation per processor.
OneOutstanding ==
    \A p \in Proc :
        Cardinality({i \in DOMAIN queue : queue[i].type = "read"
                                          /\ queue[i].proc = p}) <= 1

Safety ==
    /\ TypeOK
    /\ CacheCoherence
    /\ ResponseCoherence
    /\ ProgramOrder
    /\ FIFOOrder
    /\ NoDuplication
    /\ QueueBound
    /\ OneOutstanding

-----------------------------------------------------------------------------
(* Liveness properties *)

InQueue(id)  == \E i \in DOMAIN queue : queue[i].id = id
Dequeued(id) == \E i \in DOMAIN deqHist : deqHist[i].id = id

\* Every issued operation completes, by hit, by enqueue, or by response.
RequestCompletes ==
    \A p \in Proc : (pstate[p] # "idle") ~> (pstate[p] = "idle")

\* A pending read miss eventually receives its response.
ReadMissServed ==
    \A p \in Proc : (pstate[p] = "waitResp") ~> (resp[p].ready \/ pstate[p] = "idle")

\* Every queued request is eventually dequeued.
QueuedRequestServed ==
    \A id \in ReqId : InQueue(id) ~> Dequeued(id)

\* Every enqueued write is eventually applied to memory.
WriteEventuallyApplied ==
    \A p \in Proc, n \in 1..MaxOps :
        (\E i \in DOMAIN queue : queue[i].id = <<p, n>> /\ queue[i].type = "write")
            ~> (applied[p] >= n)

\* The queue eventually drains.
QueueDrains == []<>(queue = << >>)

Liveness ==
    /\ RequestCompletes
    /\ ReadMissServed
    /\ QueuedRequestServed
    /\ WriteEventuallyApplied
    /\ QueueDrains

THEOREM Spec => []Safety
THEOREM Spec => Liveness
=============================================================================