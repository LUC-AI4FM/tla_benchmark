------------------------- MODULE LiveInternalMemory -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, Adr, Val

VARIABLES mem, ctl, buf, memInt

vars == <<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------
(* Memory interface                                                         *)
-----------------------------------------------------------------------------
NoVal == CHOOSE v : v \notin Val

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

Send(p, d, miOld, miNew)  == miNew = <<p, d>>
Reply(p, d, miOld, miNew) == miNew = <<p, d>>

InitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

-----------------------------------------------------------------------------
(* Internal memory                                                          *)
-----------------------------------------------------------------------------
IInit == /\ mem \in [Adr -> Val]
         /\ ctl = [p \in Proc |-> "rdy"]
         /\ buf = [p \in Proc |-> NoVal]
         /\ memInt \in InitMemInt

TypeInvariant ==
  /\ mem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

Req(p) == /\ ctl[p] = "rdy"
          /\ \E req \in MReq :
                /\ Send(p, req, memInt, memInt')
                /\ buf' = [buf EXCEPT ![p] = req]
                /\ ctl' = [ctl EXCEPT ![p] = "busy"]
          /\ UNCHANGED mem

Do(p) == /\ ctl[p] = "busy"
         /\ mem' = IF buf[p].op = "Wr"
                     THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
                     ELSE mem
         /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                        THEN NoVal
                                        ELSE mem[buf[p].adr]]
         /\ ctl' = [ctl EXCEPT ![p] = "done"]
         /\ UNCHANGED memInt

Rsp(p) == /\ ctl[p] = "done"
          /\ Reply(p, buf[p], memInt, memInt')
          /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
          /\ UNCHANGED <<mem, buf>>

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

ISpec == IInit /\ [][INext]_vars

-----------------------------------------------------------------------------
(* Liveness                                                                 *)
-----------------------------------------------------------------------------
LISpec == ISpec /\ \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

Liveness == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

LivenessProperty == []Liveness

THEOREM LISpec => LivenessProperty
=============================================================================