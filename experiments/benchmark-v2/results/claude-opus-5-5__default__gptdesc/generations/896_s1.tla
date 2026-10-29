---------------------------- MODULE InternalMemory ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* Parameters of the external memory interface.                           *)
(***************************************************************************)
CONSTANTS Send(_, _, _, _),   \* Send(p, d, miOld, miNew): p sends request d
          Reply(_, _, _, _),  \* Reply(p, d, miOld, miNew): reply d to p
          InitMemInt,         \* set of possible initial values of memInt
          Proc,               \* set of processor identifiers
          Adr,                \* set of memory addresses
          Val                 \* set of memory values

VARIABLE memInt               \* the external memory interface

(***************************************************************************)
(* Memory requests and the special "no value" placeholder.                *)
(***************************************************************************)
MReq == [op : {"Rd"}, adr : Adr]
          \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

-----------------------------------------------------------------------------
(***************************************************************************)
(* Internal state of the memory component.                                *)
(***************************************************************************)
VARIABLES mem,   \* mem[a] is the current value stored at address a
          ctl,   \* ctl[p] is the control state of process p
          buf    \* buf[p] holds p's request or the value to be returned

vars == <<memInt, mem, ctl, buf>>

TypeInvariant ==
    /\ mem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
    /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

Init ==
    /\ mem \in [Adr -> Val]
    /\ ctl = [p \in Proc |-> "rdy"]
    /\ buf = [p \in Proc |-> NoVal]
    /\ memInt \in InitMemInt

(***************************************************************************)
(* Process p issues a request.                                            *)
(***************************************************************************)
Req(p) ==
    /\ ctl[p] = "rdy"
    /\ \E req \in MReq :
          /\ Send(p, req, memInt, memInt')
          /\ buf' = [buf EXCEPT ![p] = req]
          /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem

(***************************************************************************)
(* The memory performs p's pending request.                               *)
(***************************************************************************)
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

(***************************************************************************)
(* The memory returns the result to process p.                            *)
(***************************************************************************)
Rsp(p) ==
    /\ ctl[p] = "done"
    /\ Reply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>

Next == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================