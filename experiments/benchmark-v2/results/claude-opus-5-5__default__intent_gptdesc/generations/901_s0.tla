--------------------------- MODULE WriteThroughCache ---------------------------
EXTENDS Naturals, Sequences

CONSTANTS Proc,   \* set of processors
          Adr,    \* set of memory addresses
          Val,    \* set of storable values
          QLen    \* maximum length of the memory queue

ASSUME /\ QLen \in Nat
       /\ QLen > 0

VARIABLES wmem,   \* main memory: wmem[a] is the value at address a
          ctl,    \* ctl[p]: control state of processor p
          buf,    \* buf[p]: outstanding request of p, or the returned value
          cache,  \* cache[p][a]: cached value of a at p, or NoVal
          memQ    \* FIFO queue of pending memory operations <<p, req>>

vars == <<wmem, ctl, buf, cache, memQ>>

-----------------------------------------------------------------------------
NoVal == CHOOSE v : v \notin Val

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

CtlStates == {"rdy", "busy", "waiting", "done"}

-----------------------------------------------------------------------------
(* vmem: the value main memory will have after all writes currently in   *)
(* memQ have been applied, in queue order.                               *)
vmem ==
  LET f[i \in 0..Len(memQ)] ==
        IF i = 0 THEN wmem
        ELSE IF memQ[i][2].op = "Rd"
               THEN f[i-1]
               ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
  IN  f[Len(memQ)]

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ wmem \in [Adr -> Val]
  /\ ctl \in [Proc -> CtlStates]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ \in Seq(Proc \X MReq)
  /\ Len(memQ) \in 0..QLen

Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

(* Every cached value agrees with memory as it will be after all earlier *)
(* queued writes have been performed.                                     *)
CacheMatchesQueuedMemory ==
  \A p \in Proc, a \in Adr :
     (cache[p][a] # NoVal) => (cache[p][a] = vmem[a])

(* A waiting processor either has its read pending in the queue or has  *)
(* already had its cache line filled by the memory controller.           *)
WaitingConsistency ==
  \A p \in Proc :
     (ctl[p] = "waiting") =>
        /\ buf[p] \in MReq
        /\ buf[p].op = "Rd"
        /\ \/ \E i \in 1..Len(memQ) : memQ[i] = <<p, buf[p]>>
           \/ cache[p][buf[p].adr] # NoVal

-----------------------------------------------------------------------------
Init ==
  /\ wmem \in [Adr -> Val]
  /\ ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
  /\ memQ = << >>

(* Processor issues a request; main memory unchanged. *)
Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED <<wmem, cache, memQ>>

(* Processor receives its reply and becomes ready again. *)
Rsp(p) ==
  /\ ctl[p] = "done"
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<wmem, buf, cache, memQ>>

(* Read miss: enqueue the read and wait. *)
RdMiss(p) ==
  /\ ctl[p] = "busy"
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] = NoVal
  /\ Len(memQ) < QLen
  /\ memQ' = Append(memQ, <<p, buf[p]>>)
  /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<wmem, buf, cache>>

(* Read served from the cache. *)
DoRd(p) ==
  /\ ctl[p] \in {"busy", "waiting"}
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] # NoVal
  /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED <<wmem, cache, memQ>>

(* Write: update issuer's cache and any caches holding the address, enqueue. *)
DoWr(p) ==
  LET r == buf[p] IN
  /\ ctl[p] = "busy"
  /\ r.op = "Wr"
  /\ Len(memQ) < QLen
  /\ cache' = [q \in Proc |->
                 IF (p = q) \/ (cache[q][r.adr] # NoVal)
                   THEN [cache[q] EXCEPT ![r.adr] = r.val]
                   ELSE cache[q]]
  /\ memQ' = Append(memQ, <<p, r>>)
  /\ buf' = [buf EXCEPT ![p] = NoVal]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED wmem

(* Memory controller performs the write at the head of the queue. *)
MemQWr ==
  /\ memQ # << >>
  /\ LET r == Head(memQ)[2] IN
       /\ r.op = "Wr"
       /\ wmem' = [wmem EXCEPT ![r.adr] = r.val]
       /\ memQ' = Tail(memQ)
  /\ UNCHANGED <<buf, ctl, cache>>

(* Memory controller answers the read at the head of the queue, using    *)
(* the value memory will have after the queued writes are applied.       *)
MemQRd ==
  /\ memQ # << >>
  /\ LET p == Head(memQ)[1]
         r == Head(memQ)[2]
     IN  /\ r.op = "Rd"
         /\ memQ' = Tail(memQ)
         /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
  /\ UNCHANGED <<wmem, buf, ctl>>

(* Evict a single cache line. *)
Evict(p, a) ==
  /\ (ctl[p] = "waiting") => (buf[p].adr # a)
  /\ cache' = [cache EXCEPT ![p][a] = NoVal]
  /\ UNCHANGED <<wmem, buf, ctl, memQ>>

Next ==
  \/ \E p \in Proc :
        \/ Req(p)
        \/ Rsp(p)
        \/ RdMiss(p)
        \/ DoRd(p)
        \/ DoWr(p)
        \/ \E a \in Adr : Evict(p, a)
  \/ MemQWr
  \/ MemQRd

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ Coherence)
THEOREM Spec => [](CacheMatchesQueuedMemory /\ WaitingConsistency)
=============================================================================