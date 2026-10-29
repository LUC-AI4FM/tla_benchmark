---------------------------- MODULE MCInternalMemory ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Send(_, _, _, _),   \* Send(p, d, oldMemInt, newMemInt)
          Reply(_, _, _, _),  \* Reply(p, d, oldMemInt, newMemInt)
          InitMemInt,         \* set of possible initial memInt values
          Proc,               \* set of processor identifiers
          Adr,                \* set of memory addresses
          Val,                \* set of memory values
          NoVal               \* the "no value" value

ASSUME NoVal \notin Val

VARIABLES mem, ctl, buf, memInt

vars == <<mem, ctl, buf, memInt>>

-----------------------------------------------------------------------------
(* Requests a processor may issue: reads and writes.                        *)
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

(* Model-checking instantiations of the abstract interface operators.       *)
(* Each update atomically replaces the internal memory contents with the    *)
(* message payload, tagged with the identifier of the originating process.  *)
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ mem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
    /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

IInit ==
    /\ mem \in [Adr -> Val]
    /\ ctl = [p \in Proc |-> "rdy"]
    /\ buf = [p \in Proc |-> NoVal]
    /\ memInt \in InitMemInt

(* Processor p issues a request; message delivered to internal memory.      *)
Req(p) ==
    /\ ctl[p] = "rdy"
    /\ \E req \in MReq :
          /\ Send(p, req, memInt, memInt')
          /\ buf' = [buf EXCEPT ![p] = req]
          /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem

(* Internal memory performs the request of processor p.                     *)
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

(* Internal memory replies to processor p.                                  *)
Rsp(p) ==
    /\ ctl[p] = "done"
    /\ Reply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

ISpec == IInit /\ [][INext]_vars

(* Fairness: pending requests are eventually processed and answered.        *)
Liveness == \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

LISpec == ISpec /\ Liveness

-----------------------------------------------------------------------------
(* Liveness property: every issued request is eventually answered.          *)
LivenessProperty ==
    \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

=============================================================================