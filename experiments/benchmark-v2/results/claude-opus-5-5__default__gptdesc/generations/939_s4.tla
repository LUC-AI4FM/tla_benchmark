------------------------ MODULE LiveWriteThroughCache ------------------------
(***************************************************************************)
(* This module adds the liveness condition described for the write-through *)
(* cache.  It uses an equivalent definition of Spec, written out directly  *)
(* rather than through INSTANCE, so that TLC can check it.  The underlying *)
(* memory interface, internal memory and write-through cache definitions   *)
(* are included inline so that the module is self-contained.               *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Proc, Adr, Val, QLen

ASSUME (QLen \in Nat) /\ (QLen > 0)

VARIABLES memInt, wmem, ctl, buf, cache, memQ

vars == <<memInt, wmem, buf, ctl, cache, memQ>>

-----------------------------------------------------------------------------
(* Memory interface                                                        *)
-----------------------------------------------------------------------------
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

Send(p, d, miOld, miNew)  == miNew = <<p, d>>
Reply(p, d, miOld, miNew) == miNew = <<p, d>>

InitMemInt == {<<p, NoVal>> : p \in Proc}

-----------------------------------------------------------------------------
(* Write-through cache                                                     *)
-----------------------------------------------------------------------------
Init == /\ wmem \in [Adr -> Val]
        /\ ctl = [p \in Proc |-> "rdy"]
        /\ buf = [p \in Proc |-> NoVal]
        /\ memInt \in InitMemInt
        /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
        /\ memQ = <<>>

TypeInvariant ==
  /\ wmem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ \in Seq(Proc \X MReq)

Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

QueueBound == Len(memQ) <= QLen

Req(p) == /\ ctl[p] = "rdy"
          /\ \E req \in MReq :
                /\ Send(p, req, memInt, memInt')
                /\ buf' = [buf EXCEPT ![p] = req]
                /\ ctl' = [ctl EXCEPT ![p] = "busy"]
          /\ UNCHANGED <<wmem, cache, memQ>>

Rsp(p) == /\ ctl[p] = "done"
          /\ Reply(p, buf[p], memInt, memInt')
          /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
          /\ UNCHANGED <<wmem, buf, cache, memQ>>

RdMiss(p) == /\ ctl[p] = "busy"
             /\ buf[p].op = "Rd"
             /\ cache[p][buf[p].adr] = NoVal
             /\ Len(memQ) < QLen
             /\ memQ' = Append(memQ, <<p, buf[p]>>)
             /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
             /\ UNCHANGED <<memInt, wmem, buf, cache>>

DoRd(p) == /\ ctl[p] \in {"busy", "waiting"}
           /\ buf[p].op = "Rd"
           /\ cache[p][buf[p].adr] # NoVal
           /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
           /\ ctl' = [ctl EXCEPT ![p] = "done"]
           /\ UNCHANGED <<memInt, wmem, cache, memQ>>

DoWr(p) == LET r == buf[p] IN
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
           /\ UNCHANGED <<memInt, wmem>>

vmem == LET f[i \in 0..Len(memQ)] ==
              IF i = 0 THEN wmem
              ELSE IF memQ[i][2].op = "Rd"
                     THEN f[i-1]
                     ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
        IN f[Len(memQ)]

MemQWr == LET r == Head(memQ)[2] IN
          /\ memQ # <<>>
          /\ r.op = "Wr"
          /\ wmem' = [wmem EXCEPT ![r.adr] = r.val]
          /\ memQ' = Tail(memQ)
          /\ UNCHANGED <<memInt, buf, ctl, cache>>

MemQRd == LET p == Head(memQ)[1]
              r == Head(memQ)[2]
          IN  /\ memQ # <<>>
              /\ r.op = "Rd"
              /\ memQ' = Tail(memQ)
              /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
              /\ UNCHANGED <<memInt, wmem, buf, ctl>>

Evict(p, a) == /\ (ctl[p] = "waiting") => (buf[p].adr # a)
               /\ cache' = [cache EXCEPT ![p][a] = NoVal]
               /\ UNCHANGED <<memInt, wmem, buf, ctl, memQ>>

Next == \/ \E p \in Proc : \/ Req(p) \/ Rsp(p)
                           \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
                           \/ \E a \in Adr : Evict(p, a)
        \/ MemQWr
        \/ MemQRd

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Liveness                                                                *)
-----------------------------------------------------------------------------
QCond == \/ Len(memQ) = QLen
         \/ \E i \in 1..Len(memQ) : memQ[i][2].op = "Rd"

Liveness == /\ \A p \in Proc : /\ WF_vars(Rsp(p))
                               /\ WF_vars(RdMiss(p))
                               /\ WF_vars(DoRd(p))
                               /\ WF_vars(DoWr(p))
            /\ WF_vars(QCond /\ MemQWr)
            /\ WF_vars(MemQRd)

LSpec == Spec /\ Liveness

(* Every issued request is eventually answered. *)
RequestsAnswered == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

THEOREM LSpec => [](TypeInvariant /\ Coherence /\ QueueBound)
=============================================================================