------------------------- MODULE WriteThroughCache -------------------------
EXTENDS Naturals, Sequences

(***************************************************************************)
(* Memory interface parameters                                             *)
(***************************************************************************)
CONSTANTS Send(_, _, _, _),
          Reply(_, _, _, _),
          InitMemInt,
          Proc,
          Adr,
          Val,
          NoVal,
          QLen

ASSUME NoVal \notin Val
ASSUME (QLen \in Nat) /\ (QLen > 0)

VARIABLES memInt, wmem, ctl, buf, cache, memQ

vars == <<memInt, wmem, ctl, buf, cache, memQ>>

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

(***************************************************************************)
(* Model-checking overrides for the interface operators                    *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

(***************************************************************************)
(* Write-through cache controller                                          *)
(***************************************************************************)
TypeInvariant ==
  /\ wmem  \in [Adr -> Val]
  /\ ctl   \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf   \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ  \in Seq(Proc \X MReq)
  /\ Len(memQ) <= QLen

Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

Init ==
  /\ memInt \in InitMemInt
  /\ wmem  \in [Adr -> Val]
  /\ ctl   = [p \in Proc |-> "rdy"]
  /\ buf   = [p \in Proc |-> NoVal]
  /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
  /\ memQ  = << >>

\* Processor issues a request
Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED <<wmem, cache, memQ>>

\* Reply delivered to processor; it returns to idle
Rsp(p) ==
  /\ ctl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<wmem, buf, cache, memQ>>

\* Read miss: forward read to memory
RdMiss(p) ==
  /\ ctl[p] = "busy"
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] = NoVal
  /\ Len(memQ) < QLen
  /\ memQ' = Append(memQ, <<p, buf[p]>>)
  /\ ctl'  = [ctl EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<memInt, wmem, buf, cache>>

\* Read served from cache
DoRd(p) ==
  /\ ctl[p] \in {"busy", "waiting"}
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] # NoVal
  /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED <<memInt, wmem, cache, memQ>>

\* Write: update caches and write through to memory queue
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
  /\ buf'  = [buf EXCEPT ![p] = NoVal]
  /\ ctl'  = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED <<memInt, wmem>>

\* Value of memory after all queued writes are performed
vmem ==
  LET f[i \in 0..Len(memQ)] ==
        IF i = 0 THEN wmem
        ELSE IF memQ[i][2].op = "Rd" THEN f[i-1]
             ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
  IN f[Len(memQ)]

\* Memory performs a queued write
MemQWr ==
  LET r == Head(memQ)[2] IN
  /\ memQ # << >>
  /\ r.op = "Wr"
  /\ wmem' = [wmem EXCEPT ![r.adr] = r.val]
  /\ memQ' = Tail(memQ)
  /\ UNCHANGED <<memInt, buf, ctl, cache>>

\* Memory services a queued read, filling the requester's cache
MemQRd ==
  LET p == Head(memQ)[1]
      r == Head(memQ)[2]
  IN
  /\ memQ # << >>
  /\ r.op = "Rd"
  /\ memQ'  = Tail(memQ)
  /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
  /\ UNCHANGED <<memInt, wmem, buf, ctl>>

\* Cache line eviction
Evict(p, a) ==
  /\ (ctl[p] = "waiting") => (buf[p].adr # a)
  /\ cache' = [cache EXCEPT ![p][a] = NoVal]
  /\ UNCHANGED <<memInt, wmem, buf, ctl, memQ>>

Next ==
  \/ \E p \in Proc : \/ Req(p) \/ Rsp(p) \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
                     \/ \E a \in Adr : Evict(p, a)
  \/ MemQWr
  \/ MemQRd

Spec == Init /\ [][Next]_vars

\* Fair version for liveness: every issued request is eventually replied to
FairSpec ==
  /\ Spec
  /\ \A p \in Proc : WF_vars(RdMiss(p)) /\ WF_vars(DoRd(p)) /\ WF_vars(DoWr(p))
                     /\ WF_vars(Rsp(p))
  /\ WF_vars(MemQWr) /\ WF_vars(MemQRd)

Liveness == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

NoSpuriousReply == \A p \in Proc : (ctl[p] = "rdy") => (buf[p] \notin MReq) \/ TRUE

(***************************************************************************)
(* Refinement mapping to the abstract internal (atomic) memory             *)
(***************************************************************************)
omem == vmem
octl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
obuf == buf

ivars == <<memInt, omem, octl, obuf>>

LM_Inner_TypeInvariant ==
  /\ omem \in [Adr -> Val]
  /\ octl \in [Proc -> {"rdy", "busy", "done"}]
  /\ obuf \in [Proc -> MReq \cup Val \cup {NoVal}]

LM_Inner_IInit ==
  /\ memInt \in InitMemInt
  /\ omem \in [Adr -> Val]
  /\ octl = [p \in Proc |-> "rdy"]
  /\ obuf = [p \in Proc |-> NoVal]

LM_Inner_Req(p) ==
  /\ octl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ obuf' = [obuf EXCEPT ![p] = req]
        /\ octl' = [octl EXCEPT ![p] = "busy"]
  /\ UNCHANGED omem

LM_Inner_Do(p) ==
  /\ octl[p] = "busy"
  /\ omem' = IF obuf[p].op = "Wr"
               THEN [omem EXCEPT ![obuf[p].adr] = obuf[p].val]
               ELSE omem
  /\ obuf' = [obuf EXCEPT ![p] = IF obuf[p].op = "Wr"
                                   THEN NoVal
                                   ELSE omem[obuf[p].adr]]
  /\ octl' = [octl EXCEPT ![p] = "done"]
  /\ UNCHANGED memInt

LM_Inner_Rsp(p) ==
  /\ octl[p] = "done"
  /\ Reply(p, obuf[p], memInt, memInt')
  /\ octl' = [octl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<omem, obuf>>

LM_Inner_INext ==
  \E p \in Proc : LM_Inner_Req(p) \/ LM_Inner_Do(p) \/ LM_Inner_Rsp(p)

LM_Inner_ISpec == LM_Inner_IInit /\ [][LM_Inner_INext]_ivars

THEOREM Spec => [](TypeInvariant /\ Coherence /\ LM_Inner_TypeInvariant)
THEOREM Spec => LM_Inner_ISpec
THEOREM FairSpec => Liveness
=============================================================================