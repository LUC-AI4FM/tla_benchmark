---------------------------- MODULE MCInternalMemory ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Send(_, _, _, _),
          Reply(_, _, _, _),
          InitMemInt,
          Proc,
          Adr,
          Val,
          NoVal

ASSUME NoVal \notin Val

VARIABLES memInt, mem, ctl, buf

vars == <<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------
(* Model-checking instantiations of the abstract operators *)

MCSend(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

-----------------------------------------------------------------------------
(* The InternalMemory specification *)

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

TypeInvariant ==
    /\ mem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
    /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

IInit ==
    /\ mem \in [Adr -> Val]
    /\ ctl = [p \in Proc |-> "rdy"]
    /\ buf = [p \in Proc |-> NoVal]
    /\ memInt \in InitMemInt

Req(p) ==
    /\ ctl[p] = "rdy"
    /\ \E req \in MReq :
          /\ Send(p, req, memInt, memInt')
          /\ buf' = [buf EXCEPT ![p] = req]
          /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem

Do(p) ==
    /\ ctl[p] = "busy"
    /\ mem' = IF buf[p].op = "Wr"
                THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
                ELSE mem
    /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                    THEN NoVal
                                    ELSE mem[buf[p].adr]]
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED memInt

Rsp(p) ==
    /\ ctl[p] = "done"
    /\ Reply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

ISpec == IInit /\ [][INext]_vars

-----------------------------------------------------------------------------
THEOREM ISpec => []TypeInvariant
=============================================================================