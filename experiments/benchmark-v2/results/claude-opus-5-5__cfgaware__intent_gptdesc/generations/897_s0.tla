---------------------------- MODULE MCInternalMemory ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Send(_, _, _, _),
          Reply(_, _, _, _),
          InitMemInt,
          Proc,
          Adr,
          Val

VARIABLES memInt, mem, ctl, buf

vars == <<memInt, mem, ctl, buf>>

NoVal == CHOOSE v : v \notin Val

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

Payload == MReq \cup Val \cup {NoVal}

MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == { <<CHOOSE p \in Proc : TRUE, NoVal>> }

IInit == /\ mem \in [Adr -> Val]
         /\ ctl = [p \in Proc |-> "rdy"]
         /\ buf = [p \in Proc |-> NoVal]
         /\ memInt \in InitMemInt

TypeInvariant ==
    /\ mem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
    /\ buf \in [Proc -> Payload]
    /\ memInt \in Proc \X Payload

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

FairISpec == ISpec /\ WF_vars(INext)

(* The buffer channel always holds exactly one well-formed message. *)
SingleMessage ==
    /\ Len(memInt) = 2
    /\ memInt[1] \in Proc
    /\ memInt[2] \in Payload

(* Issuing a Send/Reply deterministically yields the specified pair. *)
DeterministicUpdate ==
    [][ \A p \in Proc :
          /\ (ctl[p] = "rdy" /\ ctl'[p] = "busy") => memInt' = <<p, buf'[p]>>
          /\ (ctl[p] = "done" /\ ctl'[p] = "rdy") => memInt' = <<p, buf[p]>>
      ]_vars

(* No silent loss: a busy request eventually gets a reply reflected in memInt. *)
Liveness ==
    \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")
=============================================================================