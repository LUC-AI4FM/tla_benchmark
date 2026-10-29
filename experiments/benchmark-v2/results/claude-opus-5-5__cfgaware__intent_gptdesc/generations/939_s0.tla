------------------------------ MODULE WriteThroughCache ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Parameters, defined as operators so the module is self-contained.        *)
(***************************************************************************)
NumProcs  == 2
Procs     == 1..NumProcs
Addrs     == {1, 2}
Vals      == {0, 1}
QLen      == 2              \* capacity of the memory-request queue
CacheSize == 2              \* abstract cache capacity (entries per cache)

NoVal == -1                 \* marks an invalid cache line or an empty response

Requests ==
    [type : {"R"}, proc : Procs, addr : Addrs, val : {NoVal}]
      \cup
    [type : {"W"}, proc : Procs, addr : Addrs, val : Vals]

VARIABLES
    mem,      \* shared memory: Addrs -> Vals
    cache,    \* private caches: Procs -> (Addrs -> Vals \cup {NoVal})
    queue,    \* bounded FIFO of memory requests
    pstate,   \* processor status
    resp      \* response value delivered to each processor

vars == <<mem, cache, queue, pstate, resp>>

PStates == {"idle", "rdwait", "wrwait", "rdresp"}

CacheCount(p) == Cardinality({a \in Addrs : cache[p][a] # NoVal})

TypeOK ==
    /\ mem \in [Addrs -> Vals]
    /\ cache \in [Procs -> [Addrs -> Vals \cup {NoVal}]]
    /\ queue \in Seq(Requests)
    /\ pstate \in [Procs -> PStates]
    /\ resp \in [Procs -> Vals \cup {NoVal}]

Init ==
    /\ mem = [a \in Addrs |-> 0]
    /\ cache = [p \in Procs |-> [a \in Addrs |-> NoVal]]
    /\ queue = <<>>
    /\ pstate = [p \in Procs |-> "idle"]
    /\ resp = [p \in Procs |-> NoVal]

(***************************************************************************)
(* Processor actions                                                        *)
(***************************************************************************)

\* Read hit: served locally from the private cache.
ReadHit(p, a) ==
    /\ pstate[p] = "idle"
    /\ cache[p][a] # NoVal
    /\ resp' = [resp EXCEPT ![p] = cache[p][a]]
    /\ pstate' = [pstate EXCEPT ![p] = "rdresp"]
    /\ UNCHANGED <<mem, cache, queue>>

\* Read miss: enqueue a memory read request (blocked while the queue is full).
ReadMiss(p, a) ==
    /\ pstate[p] = "idle"
    /\ cache[p][a] = NoVal
    /\ Len(queue) < QLen
    /\ queue' = Append(queue, [type |-> "R", proc |-> p, addr |-> a, val |-> NoVal])
    /\ pstate' = [pstate EXCEPT ![p] = "rdwait"]
    /\ UNCHANGED <<mem, cache, resp>>

\* Write-through: update own cache and enqueue a memory write
\* (blocked while the queue is full or the cache has no room).
Write(p, a, v) ==
    /\ pstate[p] = "idle"
    /\ Len(queue) < QLen
    /\ cache[p][a] # NoVal \/ CacheCount(p) < CacheSize
    /\ cache' = [cache EXCEPT ![p][a] = v]
    /\ queue' = Append(queue, [type |-> "W", proc |-> p, addr |-> a, val |-> v])
    /\ pstate' = [pstate EXCEPT ![p] = "wrwait"]
    /\ UNCHANGED <<mem, resp>>

\* Abstract cache replacement: any valid line may be evicted.
Evict(p, a) ==
    /\ cache[p][a] # NoVal
    /\ cache' = [cache EXCEPT ![p][a] = NoVal]
    /\ UNCHANGED <<mem, queue, pstate, resp>>

\* The processor consumes a delivered read response.
Deliver(p) ==
    /\ pstate[p] = "rdresp"
    /\ pstate' = [pstate EXCEPT ![p] = "idle"]
    /\ resp' = [resp EXCEPT ![p] = NoVal]
    /\ UNCHANGED <<mem, cache, queue>>

(***************************************************************************)
(* Memory coordinator: services the head of the FIFO queue.                *)
(***************************************************************************)
FillCache(c, a, v) ==
    \* Install v at a; if the cache is full, make room by dropping some line.
    IF c[a] # NoVal \/ Cardinality({b \in Addrs : c[b] # NoVal}) < CacheSize
    THEN {[c EXCEPT ![a] = v]}
    ELSE {[[c EXCEPT ![b] = NoVal] EXCEPT ![a] = v] :
              b \in {x \in Addrs : c[x] # NoVal}}

Serve ==
    /\ queue # <<>>
    /\ LET r == Head(queue) IN
         /\ queue' = Tail(queue)
         /\ IF r.type = "W"
            THEN /\ mem' = [mem EXCEPT ![r.addr] = r.val]
                 /\ \E nc \in FillCache(cache[r.proc], r.addr, r.val) :
                      cache' = [q \in Procs |->
                                  IF q = r.proc THEN nc
                                  ELSE [cache[q] EXCEPT ![r.addr] = NoVal]]
                 /\ pstate' = [pstate EXCEPT ![r.proc] = "idle"]  \* write ack
                 /\ UNCHANGED resp
            ELSE /\ \E nc \in FillCache(cache[r.proc], r.addr, mem[r.addr]) :
                      cache' = [cache EXCEPT ![r.proc] = nc]
                 /\ resp' = [resp EXCEPT ![r.proc] = mem[r.addr]]
                 /\ pstate' = [pstate EXCEPT ![r.proc] = "rdresp"]
                 /\ UNCHANGED mem

Next ==
    \/ \E p \in Procs, a \in Addrs :
          \/ ReadHit(p, a)
          \/ ReadMiss(p, a)
          \/ Evict(p, a)
          \/ \E v \in Vals : Write(p, a, v)
    \/ \E p \in Procs : Deliver(p)
    \/ Serve

Fairness ==
    /\ WF_vars(Serve)
    /\ \A p \in Procs : WF_vars(Deliver(p))

LSpec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety properties                                                        *)
(***************************************************************************)

\* Bounds: the queue never exceeds its capacity; caches respect their size.
QueueBound == Len(queue) <= QLen
CacheBound == \A p \in Procs : CacheCount(p) <= CacheSize

PendingWriteVal(a, v) ==
    \E i \in 1..Len(queue) :
        /\ queue[i].type = "W"
        /\ queue[i].addr = a
        /\ queue[i].val = v

\* Coherence: every valid cache value equals memory or a write that has
\* already been made visible (queued, in order, for memory).
Coherence ==
    \A p \in Procs, a \in Addrs :
        cache[p][a] # NoVal =>
            \/ cache[p][a] = mem[a]
            \/ PendingWriteVal(a, cache[p][a])

\* No loss / duplication: each waiting processor has exactly one request in
\* the queue, and idle or responding processors have none. Since a processor
\* has at most one outstanding request, its writes reach memory in program
\* order, and the queue is applied strictly in FIFO (head-first) order.
ReqCount(p) == Cardinality({i \in 1..Len(queue) : queue[i].proc = p})

NoLossNoDup ==
    \A p \in Procs :
        /\ pstate[p] \in {"rdwait", "wrwait"} => ReqCount(p) = 1
        /\ pstate[p] \in {"idle", "rdresp"}   => ReqCount(p) = 0
        /\ \A i \in 1..Len(queue) :
              queue[i].proc = p =>
                 (queue[i].type = "R" <=> pstate[p] = "rdwait")

Consistency ==
    \A p \in Procs : pstate[p] = "rdresp" => resp[p] \in Vals

Safety ==
    /\ TypeOK
    /\ QueueBound
    /\ CacheBound
    /\ Coherence
    /\ NoLossNoDup
    /\ Consistency

(***************************************************************************)
(* Liveness properties                                                      *)
(***************************************************************************)

\* Every issued request eventually completes.
RequestsComplete ==
    \A p \in Procs : (pstate[p] # "idle") ~> (pstate[p] = "idle")

\* Every pending read miss is eventually answered.
ReadMissServed ==
    \A p \in Procs : (pstate[p] = "rdwait") ~> (pstate[p] = "rdresp")

\* Every queued write is eventually applied to memory.
WritesApplied ==
    \A p \in Procs : (pstate[p] = "wrwait") ~> (pstate[p] = "idle")

\* The queue keeps draining.
QueueDrains == []<>(Len(queue) < QLen)

Liveness ==
    /\ RequestsComplete
    /\ ReadMissServed
    /\ WritesApplied
    /\ QueueDrains

THEOREM LSpec => []Safety
THEOREM LSpec => Liveness
=====================================================================================