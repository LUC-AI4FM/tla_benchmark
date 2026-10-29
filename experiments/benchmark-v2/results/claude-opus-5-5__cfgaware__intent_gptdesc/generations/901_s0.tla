--------------------------- MODULE WriteThroughCache ---------------------------
EXTENDS Naturals, Sequences

CONSTANTS Proc, Adr, Val, QLen

ASSUME (QLen \in Nat) /\ (QLen > 0)

NoVal == CHOOSE v : v \notin Val

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

VARIABLES wmem, ctl, buf, cache, memQ

vars == <<wmem, ctl, buf, cache, memQ>>

-----------------------------------------------------------------------------
(* vmem: the value main memory will hold once all queued operations finish. *)
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
  /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ \in Seq(Proc \X MReq)
  /\ Len(memQ) \leq QLen

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

(* A ready processor issues a request; memory unchanged. *)
Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED <<wmem, cache, memQ>>

(* A processor that has received its reply proceeds. *)
Rsp(p) ==
  /\ ctl[p] = "done"
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<wmem, buf, cache, memQ>>

(* Read miss: enqueue read and wait. *)
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

(* Write: update caches of writer and holders of the line, enqueue write. *)
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

(* Memory controller: apply head write to main memory. *)
MemQWr ==
  LET r == Head(memQ)[2] IN
  /\ memQ # << >>
  /\ r.op = "Wr"
  /\ wmem' = [wmem EXCEPT ![r.adr] = r.val]
  /\ memQ' = Tail(memQ)
  /\ UNCHANGED <<ctl, buf, cache>>

(* Memory controller: answer head read with value reflecting queued writes. *)
MemQRd ==
  LET p == Head(memQ)[1]
      r == Head(memQ)[2]
  IN  /\ memQ # << >>
      /\ r.op = "Rd"
      /\ memQ' = Tail(memQ)
      /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
      /\ UNCHANGED <<wmem, ctl, buf>>

(* Evict a single cache line. *)
Evict(p, a) ==
  /\ (ctl[p] = "waiting") => (buf[p].adr # a)
  /\ cache' = [cache EXCEPT ![p][a] = NoVal]
  /\ UNCHANGED <<wmem, ctl, buf, memQ>>

Next ==
  \/ \E p \in Proc : Req(p) \/ Rsp(p) \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
                     \/ \E a \in Adr : Evict(p, a)
  \/ MemQWr
  \/ MemQRd

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ Coherence)
=============================================================================