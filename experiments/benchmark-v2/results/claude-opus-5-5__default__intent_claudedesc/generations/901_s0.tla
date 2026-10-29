------------------------------ MODULE WriteThroughCache ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Proc,   \* set of processors
          Adr,    \* set of memory addresses
          Val,    \* set of possible values
          QLen    \* maximum length of the memory request queue

ASSUME QLen \in Nat /\ QLen >= 1

-----------------------------------------------------------------------------
(* Memory interface (made concrete so the module is self-contained)          *)
-----------------------------------------------------------------------------

NoVal == CHOOSE v : v \notin Val

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

\* memInt records the last interaction on the processor/memory interface.
Send(p, d, miOld, miNew)  == miNew = <<p, d>>
Reply(p, d, miOld, miNew) == miNew = <<p, d>>

InitMemInt == { <<p, NoVal>> : p \in Proc }

-----------------------------------------------------------------------------
VARIABLES memInt,  \* the processor/memory interface
          wmem,    \* main memory
          ctl,     \* control state of each processor
          buf,     \* request / response buffer of each processor
          cache,   \* cache[p][a] : value cached by p for address a, or NoVal
          memQ     \* FIFO queue of pending memory operations <<p, req>>

vars == <<memInt, wmem, ctl, buf, cache, memQ>>

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ memInt \in (Proc \X (MReq \cup Val \cup {NoVal}))
  /\ wmem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ \in Seq(Proc \X MReq)
  /\ Len(memQ) <= QLen

Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

-----------------------------------------------------------------------------
Init ==
  /\ wmem \in [Adr -> Val]
  /\ ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
  /\ memQ = << >>
  /\ memInt \in InitMemInt

\* Processor p issues a request.
Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED <<cache, memQ, wmem>>

\* Processor p receives the response to its request.
Rsp(p) ==
  /\ ctl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<cache, memQ, wmem, buf>>

\* Read miss: enqueue the read request.
RdMiss(p) ==
  /\ ctl[p] = "busy"
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] = NoVal
  /\ Len(memQ) < QLen
  /\ memQ' = Append(memQ, <<p, buf[p]>>)
  /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<memInt, wmem, buf, cache>>

\* Read hit: return the cached value.
DoRd(p) ==
  /\ ctl[p] \in {"busy", "waiting"}
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] # NoVal
  /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED <<memInt, wmem, cache, memQ>>

\* Write-through: update own cache and other caches holding the address,
\* and enqueue the write to main memory.
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
      /\ buf' = [buf EXCEPT ![p] = NoVal]
      /\ ctl' = [ctl EXCEPT ![p] = "done"]
      /\ UNCHANGED <<memInt, wmem>>

\* The value memory will have once all queued writes have been performed.
vmem ==
  LET f[i \in 0 .. Len(memQ)] ==
        IF i = 0 THEN wmem
        ELSE IF memQ[i][2].op = "Rd"
               THEN f[i-1]
               ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
  IN  f[Len(memQ)]

\* Process a write at the head of the queue.
MemQWr ==
  LET r == Head(memQ)[2]
  IN  /\ memQ # << >>
      /\ r.op = "Wr"
      /\ wmem' = [wmem EXCEPT ![r.adr] = r.val]
      /\ memQ' = Tail(memQ)
      /\ UNCHANGED <<memInt, buf, ctl, cache>>

\* Process a read at the head of the queue.
MemQRd ==
  LET p == Head(memQ)[1]
      r == Head(memQ)[2]
  IN  /\ memQ # << >>
      /\ r.op = "Rd"
      /\ memQ' = Tail(memQ)
      /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
      /\ UNCHANGED <<memInt, wmem, buf, ctl>>

\* Evict a cache entry (not one a pending read is waiting for).
Evict(p, a) ==
  /\ (ctl[p] = "waiting") => (buf[p].adr # a)
  /\ cache' = [cache EXCEPT ![p][a] = NoVal]
  /\ UNCHANGED <<memInt, wmem, buf, ctl, memQ>>

Next ==
  \/ \E p \in Proc :
        \/ Req(p) \/ Rsp(p) \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
        \/ \E a \in Adr : Evict(p, a)
  \/ MemQWr
  \/ MemQRd

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Abstract linearizable memory (InternalMemory) under the refinement        *)
(* mapping  mem <- vmem,  ctl <- actl,  buf <- buf,  memInt <- memInt         *)
-----------------------------------------------------------------------------

actl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]

IInit ==
  /\ vmem \in [Adr -> Val]
  /\ actl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

IReq(p) ==
  /\ actl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ actl' = [actl EXCEPT ![p] = "busy"]
  /\ vmem' = vmem

IDo(p) ==
  /\ actl[p] = "busy"
  /\ vmem' = IF buf[p].op = "Wr"
               THEN [vmem EXCEPT ![buf[p].adr] = buf[p].val]
               ELSE vmem
  /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                 THEN NoVal
                                 ELSE vmem[buf[p].adr]]
  /\ actl' = [actl EXCEPT ![p] = "done"]
  /\ memInt' = memInt

IRsp(p) ==
  /\ actl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ actl' = [actl EXCEPT ![p] = "rdy"]
  /\ vmem' = vmem
  /\ buf' = buf

INext == \E p \in Proc : IReq(p) \/ IDo(p) \/ IRsp(p)

ISpec == IInit /\ [][INext]_<<memInt, vmem, actl, buf>>

\* Linearizability: the write-through cache implements the linearizable memory.
Linearizability == ISpec

THEOREM Spec => [](TypeInvariant /\ Coherence)
THEOREM Spec => Linearizability
=============================================================================