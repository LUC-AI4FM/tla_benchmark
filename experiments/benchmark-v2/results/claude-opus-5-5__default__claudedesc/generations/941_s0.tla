------------------------- MODULE MCLiveWriteThroughCache -------------------------
(***************************************************************************)
(* Model-checking configuration that checks that the live write-through   *)
(* cache (LSpec) implements the live internal memory specification under  *)
(* the refinement mapping                                                  *)
(*      omem <- vmem,                                                      *)
(*      octl <- ctl with "waiting" replaced by "busy",                     *)
(*      obuf <- buf.                                                       *)
(* The LiveWriteThroughCache content is included inline so that the       *)
(* module is self-contained.                                               *)
(*                                                                         *)
(* Intended TLC model:                                                     *)
(*   Proc <- {p1, p2}, Adr <- {a1}, Val <- {v1, v2}, NoVal <- NoVal,       *)
(*   QLen <- 1                                                             *)
(*   SPECIFICATION LSpec                                                   *)
(*   PROPERTIES LM_Inner_LISpec LM_Inner_Liveness                          *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Proc, Adr, Val, NoVal, QLen

ASSUME /\ NoVal \notin Val
       /\ QLen \in Nat
       /\ QLen > 0

VARIABLES memInt, wmem, ctl, buf, cache, memQ

vars == <<memInt, wmem, ctl, buf, cache, memQ>>

-----------------------------------------------------------------------------
(*************************** Memory interface *****************************)

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

Send(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
Reply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

InitMemInt == {<<p, NoVal>> : p \in Proc}

-----------------------------------------------------------------------------
(************************* Write-through cache ****************************)

Init == /\ wmem \in [Adr -> Val]
        /\ ctl = [p \in Proc |-> "rdy"]
        /\ buf = [p \in Proc |-> NoVal]
        /\ memInt \in InitMemInt
        /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
        /\ memQ = << >>

TypeInvariant ==
  /\ wmem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ \in Seq(Proc \X MReq)
  /\ Len(memQ) <= QLen

Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

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

DoWr(p) == /\ ctl[p] = "busy"
           /\ buf[p].op = "Wr"
           /\ Len(memQ) < QLen
           /\ LET r == buf[p] IN
                /\ cache' = [q \in Proc |->
                               IF (p = q) \/ (cache[q][r.adr] # NoVal)
                                 THEN [cache[q] EXCEPT ![r.adr] = r.val]
                                 ELSE cache[q]]
                /\ memQ' = Append(memQ, <<p, r>>)
           /\ buf' = [buf EXCEPT ![p] = NoVal]
           /\ ctl' = [ctl EXCEPT ![p] = "done"]
           /\ UNCHANGED <<memInt, wmem>>

vmem ==
  LET f[i \in 0..Len(memQ)] ==
        IF i = 0 THEN wmem
        ELSE IF memQ[i][2].op = "Rd"
               THEN f[i-1]
               ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
  IN  f[Len(memQ)]

MemQWr == /\ memQ # << >>
          /\ Head(memQ)[2].op = "Wr"
          /\ LET r == Head(memQ)[2] IN
                wmem' = [wmem EXCEPT ![r.adr] = r.val]
          /\ memQ' = Tail(memQ)
          /\ UNCHANGED <<memInt, buf, ctl, cache>>

MemQRd == /\ memQ # << >>
          /\ Head(memQ)[2].op = "Rd"
          /\ LET p == Head(memQ)[1]
                 r == Head(memQ)[2]
             IN  cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
          /\ memQ' = Tail(memQ)
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
(******************** Live write-through cache ****************************)

Liveness ==
  /\ \A p \in Proc :
        /\ SF_vars(RdMiss(p) \/ DoRd(p) \/ DoWr(p))
        /\ WF_vars(Rsp(p))
  /\ WF_vars(MemQWr \/ MemQRd)

LSpec == Spec /\ Liveness

-----------------------------------------------------------------------------
(************************** Refinement mapping ****************************)

omem == vmem
octl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
obuf == buf

ovars == <<memInt, omem, octl, obuf>>

(****************** LM_Inner: live internal memory ************************)

LM_Inner_IInit ==
  /\ omem \in [Adr -> Val]
  /\ octl = [p \in Proc |-> "rdy"]
  /\ obuf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

LM_Inner_TypeInvariant ==
  /\ omem \in [Adr -> Val]
  /\ octl \in [Proc -> {"rdy", "busy", "done"}]
  /\ obuf \in [Proc -> MReq \cup Val \cup {NoVal}]

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

LM_Inner_ISpec == LM_Inner_IInit /\ [][LM_Inner_INext]_ovars

LM_Inner_Liveness ==
  \A p \in Proc : /\ WF_ovars(LM_Inner_Do(p))
                  /\ WF_ovars(LM_Inner_Rsp(p))

LM_Inner_Liveness2 ==
  \A p \in Proc : WF_ovars(LM_Inner_Do(p) \/ LM_Inner_Rsp(p))

LM_Inner_LISpec == LM_Inner_ISpec /\ LM_Inner_Liveness2

-----------------------------------------------------------------------------
(*************************** Properties checked ***************************)

THEOREM LSpec => [](TypeInvariant /\ Coherence)
THEOREM LSpec => LM_Inner_LISpec
THEOREM LSpec => LM_Inner_Liveness
=============================================================================