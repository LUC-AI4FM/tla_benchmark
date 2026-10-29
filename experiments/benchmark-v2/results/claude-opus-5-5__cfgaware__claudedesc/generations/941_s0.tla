------------------------- MODULE MCLiveWriteThroughCache -------------------------
EXTENDS Naturals, Sequences

CONSTANTS Send(_, _, _, _),
          Reply(_, _, _, _),
          InitMemInt,
          Proc,
          Adr,
          Val,
          NoVal,
          QLen

ASSUME NoVal \notin Val

VARIABLES memInt, wmem, ctl, buf, cache, memQ

vars == <<memInt, wmem, ctl, buf, cache, memQ>>

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

-----------------------------------------------------------------------------
(* Model-checking overrides for the memory-interface constants              *)
-----------------------------------------------------------------------------
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

-----------------------------------------------------------------------------
(* Write-through cache                                                      *)
-----------------------------------------------------------------------------
Init == /\ wmem \in [Adr -> Val]
        /\ ctl = [p \in Proc |-> "rdy"]
        /\ buf = [p \in Proc |-> NoVal]
        /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
        /\ memQ = << >>
        /\ memInt \in InitMemInt

TypeInvariant ==
  /\ wmem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ \in Seq(Proc \X MReq)

Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

Req(p) == /\ ctl[p] = "rdy"
          /\ \E req \in MReq :
                /\ Send(p, req, memInt, memInt')
                /\ buf' = [buf EXCEPT ![p] = req]
                /\ ctl' = [ctl EXCEPT ![p] = "busy"]
          /\ UNCHANGED <<cache, memQ, wmem>>

Rsp(p) == /\ ctl[p] = "done"
          /\ Reply(p, buf[p], memInt, memInt')
          /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
          /\ UNCHANGED <<cache, memQ, wmem, buf>>

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

DoWr(p) == LET r == buf[p]
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

vmem ==
  LET f[i \in 0 .. Len(memQ)] ==
        IF i = 0 THEN wmem
                 ELSE IF memQ[i][2].op = "Rd"
                        THEN f[i - 1]
                        ELSE [f[i - 1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
  IN  f[Len(memQ)]

MemQWr == /\ memQ # << >>
          /\ Head(memQ)[2].op = "Wr"
          /\ wmem' = [wmem EXCEPT ![Head(memQ)[2].adr] = Head(memQ)[2].val]
          /\ memQ' = Tail(memQ)
          /\ UNCHANGED <<memInt, buf, ctl, cache>>

MemQRd == /\ memQ # << >>
          /\ Head(memQ)[2].op = "Rd"
          /\ memQ' = Tail(memQ)
          /\ cache' = [cache EXCEPT ![Head(memQ)[1]][Head(memQ)[2].adr] =
                                       vmem[Head(memQ)[2].adr]]
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
(* Live write-through cache                                                 *)
-----------------------------------------------------------------------------
Liveness ==
  /\ WF_vars(MemQWr \/ MemQRd)
  /\ \A p \in Proc : /\ SF_vars(RdMiss(p) \/ DoRd(p) \/ DoWr(p))
                     /\ WF_vars(Rsp(p))

LSpec == Spec /\ Liveness

-----------------------------------------------------------------------------
(* Refinement mapping                                                       *)
-----------------------------------------------------------------------------
omem == vmem
octl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
obuf == buf

ivars == <<memInt, omem, octl, obuf>>

-----------------------------------------------------------------------------
(* Live internal memory specification under the refinement mapping          *)
-----------------------------------------------------------------------------
LM_Inner_IInit ==
  /\ omem \in [Adr -> Val]
  /\ octl = [p \in Proc |-> "rdy"]
  /\ obuf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

LM_Inner_Req(p) ==
  /\ octl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ obuf' = [obuf EXCEPT ![p] = req]
        /\ octl' = [octl EXCEPT ![p] = "busy"]
  /\ omem' = omem

LM_Inner_Do(p) ==
  /\ octl[p] = "busy"
  /\ omem' = IF obuf[p].op = "Wr"
               THEN [omem EXCEPT ![obuf[p].adr] = obuf[p].val]
               ELSE omem
  /\ obuf' = [obuf EXCEPT ![p] = IF obuf[p].op = "Wr"
                                   THEN NoVal
                                   ELSE omem[obuf[p].adr]]
  /\ octl' = [octl EXCEPT ![p] = "done"]
  /\ memInt' = memInt

LM_Inner_Rsp(p) ==
  /\ octl[p] = "done"
  /\ Reply(p, obuf[p], memInt, memInt')
  /\ octl' = [octl EXCEPT ![p] = "rdy"]
  /\ omem' = omem
  /\ obuf' = obuf

LM_Inner_INext ==
  \E p \in Proc : LM_Inner_Req(p) \/ LM_Inner_Do(p) \/ LM_Inner_Rsp(p)

LM_Inner_ISpec == LM_Inner_IInit /\ [][LM_Inner_INext]_ivars

(* Weak fairness written as  []<>~ENABLED <<A>>_v  \/  []<><<A>>_v .        *)
(* In the internal memory, <<Do(p)>>_v is enabled exactly when ctl[p] is   *)
(* "busy", and <<Rsp(p)>>_v exactly when ctl[p] is "done" (Reply being     *)
(* always satisfiable, as with MCReply).                                    *)
LM_Inner_Liveness ==
  \A p \in Proc :
     /\ ([]<>(octl[p] # "busy") \/ []<><<LM_Inner_Do(p)>>_ivars)
     /\ ([]<>(octl[p] # "done") \/ []<><<LM_Inner_Rsp(p)>>_ivars)

LM_Inner_Liveness2 ==
  \A p \in Proc :
     []<>(octl[p] \notin {"busy", "done"})
        \/ []<><<LM_Inner_Do(p) \/ LM_Inner_Rsp(p)>>_ivars

LM_Inner_LISpec == LM_Inner_ISpec /\ LM_Inner_Liveness

=============================================================================