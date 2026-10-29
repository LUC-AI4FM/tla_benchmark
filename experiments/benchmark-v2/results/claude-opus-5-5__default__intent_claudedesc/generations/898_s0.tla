------------------------- MODULE WriteThroughCache -------------------------
EXTENDS Naturals, Sequences

(***************************************************************************)
(* Memory interface parameters                                             *)
(***************************************************************************)
CONSTANTS Send(_, _, _, _),   \* Send(p, req, miOld, miNew): processor p sends req
          Reply(_, _, _, _),  \* Reply(p, val, miOld, miNew): reply val to p
          InitMemInt,         \* set of possible initial values of memInt
          Proc,               \* set of processors
          Adr,                \* set of memory addresses
          Val,                \* set of memory values
          QLen                \* maximum length of the memory request queue

ASSUME (QLen \in Nat) /\ (QLen > 0)

VARIABLE memInt

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

(***************************************************************************)
(* Write-through cache state                                               *)
(***************************************************************************)
VARIABLES wmem,   \* main memory (backing store)
          ctl,    \* processor control state
          buf,    \* per-processor request / response buffer
          cache,  \* cache[p][a]: cached value of address a for processor p
          memQ    \* queue of <<proc, request>> pairs pending at main memory

vars == <<memInt, wmem, ctl, buf, cache, memQ>>

TypeInvariant ==
  /\ wmem  \in [Adr -> Val]
  /\ ctl   \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf   \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ  \in Seq(Proc \X MReq)
  /\ Len(memQ) <= QLen

(***************************************************************************)
(* Coherence: any two processors caching the same address hold equal values*)
(***************************************************************************)
Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

Init ==
  /\ wmem \in [Adr -> Val]
  /\ ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
  /\ memQ = << >>
  /\ memInt \in InitMemInt

(* Processor p issues a request *)
Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED <<wmem, cache, memQ>>

(* The response is returned to processor p *)
Rsp(p) ==
  /\ ctl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<wmem, buf, cache, memQ>>

(* Read miss: enqueue a read request to main memory *)
RdMiss(p) ==
  /\ ctl[p] = "busy"
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] = NoVal
  /\ Len(memQ) < QLen
  /\ memQ' = Append(memQ, <<p, buf[p]>>)
  /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<memInt, wmem, buf, cache>>

(* Perform a read from the cache *)
DoRd(p) ==
  /\ ctl[p] \in {"busy", "waiting"}
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] # NoVal
  /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED <<memInt, wmem, cache, memQ>>

(* Write: update caches holding the address and enqueue to main memory *)
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

(* Value memory will have after all queued writes are performed *)
vmem ==
  LET f[i \in 0 .. Len(memQ)] ==
        IF i = 0 THEN wmem
        ELSE IF memQ[i][2].op = "Rd"
               THEN f[i-1]
               ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
  IN  f[Len(memQ)]

(* Main memory performs the write at the head of the queue *)
MemQWr ==
  LET r == Head(memQ)[2]
  IN  /\ memQ # << >>
      /\ r.op = "Wr"
      /\ wmem' = [wmem EXCEPT ![r.adr] = r.val]
      /\ memQ' = Tail(memQ)
      /\ UNCHANGED <<memInt, buf, ctl, cache>>

(* Main memory services the read at the head of the queue *)
MemQRd ==
  LET p == Head(memQ)[1]
      r == Head(memQ)[2]
  IN  /\ memQ # << >>
      /\ r.op = "Rd"
      /\ memQ' = Tail(memQ)
      /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
      /\ UNCHANGED <<memInt, wmem, buf, ctl>>

(* Evict an address from p's cache *)
Evict(p, a) ==
  /\ (ctl[p] = "waiting") => (buf[p].adr # a)
  /\ cache' = [cache EXCEPT ![p][a] = NoVal]
  /\ UNCHANGED <<memInt, wmem, buf, ctl, memQ>>

Next ==
  \/ \E p \in Proc :
        \/ Req(p) \/ Rsp(p)
        \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
        \/ \E a \in Adr : Evict(p, a)
  \/ MemQWr
  \/ MemQRd

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Fairness and liveness: every request is eventually serviced             *)
(***************************************************************************)
Fairness ==
  /\ \A p \in Proc : SF_vars(DoRd(p)) /\ SF_vars(RdMiss(p)) /\ SF_vars(DoWr(p))
  /\ WF_vars(MemQWr)
  /\ WF_vars(MemQRd)

FairSpec == Spec /\ Fairness

Liveness == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "done")

(***************************************************************************)
(* Refinement mapping to the simple internal memory specification          *)
(***************************************************************************)
omem == vmem
octl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
obuf == buf

ovars == <<memInt, omem, octl, obuf>>

IMTypeInvariant ==
  /\ omem \in [Adr -> Val]
  /\ octl \in [Proc -> {"rdy", "busy", "done"}]
  /\ obuf \in [Proc -> MReq \cup Val \cup {NoVal}]

IMInit ==
  /\ omem \in [Adr -> Val]
  /\ octl = [p \in Proc |-> "rdy"]
  /\ obuf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

IMReq(p) ==
  /\ octl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ obuf' = [obuf EXCEPT ![p] = req]
        /\ octl' = [octl EXCEPT ![p] = "busy"]
  /\ omem' = omem

IMDo(p) ==
  /\ octl[p] = "busy"
  /\ omem' = IF obuf[p].op = "Wr"
               THEN [omem EXCEPT ![obuf[p].adr] = obuf[p].val]
               ELSE omem
  /\ obuf' = [obuf EXCEPT ![p] = IF obuf[p].op = "Wr"
                                   THEN NoVal
                                   ELSE omem[obuf[p].adr]]
  /\ octl' = [octl EXCEPT ![p] = "done"]
  /\ memInt' = memInt

IMRsp(p) ==
  /\ octl[p] = "done"
  /\ Reply(p, obuf[p], memInt, memInt')
  /\ octl' = [octl EXCEPT ![p] = "rdy"]
  /\ omem' = omem
  /\ obuf' = obuf

IMNext == \E p \in Proc : IMReq(p) \/ IMDo(p) \/ IMRsp(p)

IMSpec == IMInit /\ [][IMNext]_ovars

THEOREM Spec => [](TypeInvariant /\ Coherence)
THEOREM Spec => IMSpec
THEOREM FairSpec => Liveness
=============================================================================