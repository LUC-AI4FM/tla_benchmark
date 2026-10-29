------------------------- MODULE MCLiveInternalMemory -------------------------
(***************************************************************************)
(* Internal memory specification with liveness, together with the         *)
(* definitions needed to instantiate the memory interface for model        *)
(* checking.                                                               *)
(***************************************************************************)

CONSTANTS Send(_, _, _, _),   \* Send(p, d, miOld, miNew): processor p sends request d
          Reply(_, _, _, _),  \* Reply(p, d, miOld, miNew): memory replies d to p
          InitMemInt,         \* set of possible initial values of memInt
          Proc,               \* set of processors
          Adr,                \* set of memory addresses
          Val,                \* set of memory values
          NoVal               \* a value that is not in Val

ASSUME NoVal \notin Val

VARIABLE memInt

-----------------------------------------------------------------------------
(* Memory interface definitions *)

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

-----------------------------------------------------------------------------
(* Internal memory *)

VARIABLES mem, ctl, buf

vars == <<memInt, mem, ctl, buf>>

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
(* Liveness *)

Liveness == \A p \in Proc : /\ WF_vars(Do(p))
                            /\ WF_vars(Rsp(p))

LISpec == ISpec /\ Liveness

\* Every issued request eventually gets a reply: a processor that is not
\* ready (request pending) eventually returns to the ready state.
LivenessProperty == \A p \in Proc : (ctl[p] # "rdy") ~> (ctl[p] = "rdy")

-----------------------------------------------------------------------------
(* Model-checking instantiation of the interface *)

MCSend(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

=============================================================================