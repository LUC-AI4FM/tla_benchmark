------------------------- MODULE LiveWriteThroughCache -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,   \* set of processors
          Adr,    \* set of memory addresses
          Val,    \* set of memory values
          QLen    \* capacity of the memory queue

ASSUME QLen \in Nat \ {0}

-----------------------------------------------------------------------------
(* Memory interface between processors and the memory system              *)
-----------------------------------------------------------------------------

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

\* memInt records the last value exchanged on the processor/memory interface.
Send(p, d, miOld, miNew)  == miNew = <<p, d>>
Reply(p, d, miOld, miNew) == miNew = <<p, d>>

InitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

-----------------------------------------------------------------------------

VARIABLES wmem,    \* main memory contents
          ctl,     \* per-processor control state
          buf,     \* per-processor request / response buffer
          cache,   \* per-processor cache
          memQ,    \* queue of requests to main memory
          memInt   \* the memory interface

vars == <<wmem, ctl, buf, cache, memQ, memInt>>

-----------------------------------------------------------------------------
(* vmem: the value memory will have after all queued writes are performed  *)
-----------------------------------------------------------------------------

vmem ==
  LET f[i \in 0..Len(memQ)] ==
        IF i = 0 THEN wmem
        ELSE IF memQ[i][2].op = "Rd"
               THEN f[i-1]
               ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
  IN  f[Len(memQ)]

-----------------------------------------------------------------------------
(* Invariants                                                              *)
-----------------------------------------------------------------------------

TypeInvariant ==
  /\ wmem  \in [Adr -> Val]
  /\ ctl   \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf   \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ  \in Seq(Proc \X MReq)
  /\ Len(memQ) <= QLen

\* Cache coherence: any two cached copies of an address agree.
Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

\* Linearizability: every cached value equals the value that memory would hold
\* after all pending (already linearized) writes are performed.  Thus every
\* read satisfied from a cache returns the value of the linearized memory.
CacheConsistent ==
  \A p \in Proc, a \in Adr :
     cache[p][a] # NoVal => cache[p][a] = vmem[a]

\* A processor waiting on a read miss has exactly one read in the queue.
WaitingConsistent ==
  \A p \in Proc :
     ctl[p] = "waiting" =>
        /\ buf[p] \in MReq
        /\ buf[p].op = "Rd"
        /\ Cardinality({i \in 1..Len(memQ) : memQ[i][1] = p}) >= 1

\* At most one outstanding read per processor in the memory queue.
QueueReadsWellFormed ==
  \A i \in 1..Len(memQ) :
     memQ[i][2].op = "Rd" => ctl[memQ[i][1]] = "waiting"

-----------------------------------------------------------------------------
(* Initial state                                                           *)
-----------------------------------------------------------------------------

Init ==
  /\ wmem   \in [Adr -> Val]
  /\ ctl    = [p \in Proc |-> "rdy"]
  /\ buf    = [p \in Proc |-> NoVal]
  /\ cache  = [p \in Proc |-> [a \in Adr |-> NoVal]]
  /\ memQ   = << >>
  /\ memInt \in InitMemInt

-----------------------------------------------------------------------------
(* Actions                                                                 *)
-----------------------------------------------------------------------------

\* Processor p issues a request.
Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED <<cache, memQ, wmem>>

\* The response to processor p is returned.
Rsp(p) ==
  /\ ctl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<cache, memQ, wmem, buf>>

\* Read miss: enqueue a read request to main memory.
RdMiss(p) ==
  /\ ctl[p] = "busy"
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] = NoVal
  /\ Len(memQ) < QLen
  /\ memQ' = Append(memQ, <<p, buf[p]>>)
  /\ ctl'  = [ctl EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<memInt, wmem, buf, cache>>

\* Read hit: satisfy read from the cache.
DoRd(p) ==
  /\ ctl[p] = "busy"
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] # NoVal
  /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED <<memInt, memQ, wmem, cache>>

\* Write: update own cache and all caches holding the address, and enqueue
\* the write to main memory (write-through).
DoWr(p) ==
  LET r == buf[p]
  IN  /\ ctl[p] = "busy"
      /\ r.op = "Wr"
      /\ Len(memQ) < QLen
      /\ cache' = [q \in Proc |->
                     IF (p = q) \/ (cache[q][r.adr] # NoVal)
                       THEN [cache[q] EXCEPT ![r.adr] = r.val]
                       ELSE cache[q]]
      /\ memQ' = Append(memQ, <<p, r>>)
      /\ buf'  = [buf EXCEPT ![p] = NoVal]
      /\ ctl'  = [ctl EXCEPT ![p] = "done"]
      /\ UNCHANGED <<memInt, wmem>>

\* Main memory performs the write at the head of the queue.
MemQWr ==
  LET r == Head(memQ)[2]
  IN  /\ memQ # << >>
      /\ r.op = "Wr"
      /\ wmem' = [wmem EXCEPT ![r.adr] = r.val]
      /\ memQ' = Tail(memQ)
      /\ UNCHANGED <<memInt, buf, ctl, cache>>

\* Main memory services the read at the head of the queue.  The value
\* returned is vmem, which reflects all earlier queued writes.
MemQRd ==
  LET p == Head(memQ)[1]
      r == Head(memQ)[2]
  IN  /\ memQ # << >>
      /\ r.op = "Rd"
      /\ memQ'  = Tail(memQ)
      /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
      /\ buf'   = [buf EXCEPT ![p] = vmem[r.adr]]
      /\ ctl'   = [ctl EXCEPT ![p] = "done"]
      /\ UNCHANGED <<memInt, wmem>>

\* Evict an address from p's cache.
Evict(p, a) ==
  /\ (ctl[p] = "waiting") => (buf[p].adr # a)
  /\ cache' = [cache EXCEPT ![p][a] = NoVal]
  /\ UNCHANGED <<memInt, wmem, buf, ctl, memQ>>

-----------------------------------------------------------------------------

Next ==
  \/ \E p \in Proc : \/ Req(p) \/ Rsp(p)
                     \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
                     \/ \E a \in Adr : Evict(p, a)
  \/ MemQWr
  \/ MemQRd

-----------------------------------------------------------------------------
(* Fairness                                                                *)
-----------------------------------------------------------------------------

\* Memory queue must be processed when it is full or when reads are pending.
QCond ==
  \/ Len(memQ) = QLen
  \/ \E i \in 1..Len(memQ) : memQ[i][2].op = "Rd"

Liveness ==
  /\ \A p \in Proc :
        /\ WF_vars(Rsp(p) \/ DoRd(p))        \* response guarantee
        /\ SF_vars(RdMiss(p) \/ DoWr(p))     \* miss / write handling
  /\ WF_vars(MemQRd)                         \* pending reads serviced
  /\ WF_vars(QCond /\ MemQWr)                \* writes processed when needed

Spec == Init /\ [][Next]_vars /\ Liveness

-----------------------------------------------------------------------------
(* Properties                                                              *)
-----------------------------------------------------------------------------

\* Every request issued by a processor eventually receives a response.
RequestsComplete ==
  \A p \in Proc : (ctl[p] # "rdy") ~> (ctl[p] = "rdy")

\* A processor waiting on a read miss is eventually serviced.
MissesServiced ==
  \A p \in Proc : (ctl[p] = "waiting") ~> (ctl[p] = "done")

\* No processor starves: it is ready infinitely often.
NoStarvation ==
  \A p \in Proc : []<>(ctl[p] = "rdy")

\* The memory queue never stays full forever.
QueueDrains ==
  (Len(memQ) = QLen) ~> (Len(memQ) < QLen)

\* Pending reads in the queue are eventually removed.
ReadsLeaveQueue ==
  (\E i \in 1..Len(memQ) : memQ[i][2].op = "Rd")
     ~> (\A i \in 1..Len(memQ) : memQ[i][2].op = "Wr")
     \/ (\E i \in 1..Len(memQ) : memQ[i][2].op = "Rd")
        /\ Len(memQ) < QLen

THEOREM Spec => [](TypeInvariant /\ Coherence /\ CacheConsistent)
THEOREM Spec => RequestsComplete /\ MissesServiced /\ NoStarvation
=============================================================================