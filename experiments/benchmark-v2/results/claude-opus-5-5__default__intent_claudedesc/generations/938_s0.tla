------------------------- MODULE LiveInternalMemory -------------------------
EXTENDS Naturals

CONSTANTS Proc,   \* The set of processors
          Adr,    \* The set of memory addresses
          Val     \* The set of memory values

VARIABLES mem,    \* mem[a] is the value stored at address a
          ctl,    \* ctl[p] is "rdy", "busy", or "done"
          buf,    \* buf[p] holds p's request or the response to it
          memInt  \* The memory interface (the last message sent/received)

vars == <<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------
(* Memory interface definitions                                            *)
-----------------------------------------------------------------------------
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

Send(p, d, miOld, miNew)  == miNew = <<p, d>>
Reply(p, d, miOld, miNew) == miNew = <<p, d>>

InitMemInt == {<<>>}

-----------------------------------------------------------------------------
(* Internal memory: safety part                                            *)
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

\* Processor p issues a request
Req(p) ==
    /\ ctl[p] = "rdy"
    /\ \E req \in MReq :
          /\ Send(p, req, memInt, memInt')
          /\ buf' = [buf EXCEPT ![p] = req]
          /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem

\* The memory performs p's request
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

\* The memory returns the response to p
Rsp(p) ==
    /\ ctl[p] = "done"
    /\ Reply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

ISpec == IInit /\ [][INext]_vars

-----------------------------------------------------------------------------
(* Liveness: fairness conditions                                           *)
-----------------------------------------------------------------------------
Liveness == \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

Init == IInit
Next == INext

LSpec == ISpec /\ Liveness
Spec  == LSpec

-----------------------------------------------------------------------------
(* Properties                                                              *)
-----------------------------------------------------------------------------
\* Guaranteed response: every busy processor eventually becomes ready again
LivenessProperty == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

THEOREM LSpec => []TypeInvariant
THEOREM LSpec => LivenessProperty
=============================================================================