------------------------------ MODULE InternalMemory ------------------------------
(***************************************************************************)
(* Internal memory specification: a set of processors issue Read/Write    *)
(* requests to a shared memory through a memory interface (memInt), and   *)
(* the memory sends replies back through the same interface.              *)
(*                                                                         *)
(* The communication primitives Send and Reply are given concrete         *)
(* definitions so the spec can be model checked with TLC. They record     *)
(* the full message (processor, payload) in memInt. To reduce the state   *)
(* space, Send/Reply can be redefined to record less, for example         *)
(* newMemInt = p (only who communicated) or UNCHANGED (newMemInt =        *)
(* oldMemInt). The rest of the spec does not depend on that choice.       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Proc,     \* set of processors
          Adr,      \* set of memory addresses
          Val,      \* set of memory values
          NoVal     \* value returned as the reply to a Write

ASSUME NoVal \notin Val

-----------------------------------------------------------------------------
(***************************************************************************)
(* Requests and replies                                                    *)
(***************************************************************************)
MReq == [op : {"Rd"}, adr : Adr]
          \cup [op : {"Wr"}, adr : Adr, val : Val]

ReplyVals == Val \cup {NoVal}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete memory interface (communication medium)                        *)
(***************************************************************************)
MemIntVals == (Proc \X (MReq \cup ReplyVals)) \cup {<<"none", NoVal>>}

InitMemInt == {<<"none", NoVal>>}

\* Processor p sends request/data d. The interface changes from
\* oldMemInt to newMemInt.
Send(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

\* Memory sends reply d back to processor p. The interface changes from
\* oldMemInt to newMemInt.
Reply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

-----------------------------------------------------------------------------
VARIABLES memInt,   \* the memory interface
          mem,      \* mem[a] = current value of memory location a
          ctl,      \* ctl[p] \in {"rdy", "busy", "done"}
          buf       \* buf[p] = pending request, or the reply to deliver

vars == <<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ memInt \in MemIntVals
    /\ mem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
    /\ buf \in [Proc -> MReq \cup ReplyVals]

Init ==
    /\ memInt \in InitMemInt
    /\ mem \in [Adr -> Val]
    /\ ctl = [p \in Proc |-> "rdy"]
    /\ buf = [p \in Proc |-> NoVal]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Processor p issues a request through the memory interface.              *)
(***************************************************************************)
Req(p) ==
    /\ ctl[p] = "rdy"
    /\ \E req \in MReq :
          /\ Send(p, req, memInt, memInt')
          /\ buf' = [buf EXCEPT ![p] = req]
          /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem

(***************************************************************************)
(* The memory performs processor p's pending request.                      *)
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
(* The memory replies to processor p through the memory interface.         *)
(***************************************************************************)
Rsp(p) ==
    /\ ctl[p] = "done"
    /\ Reply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>

Next == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

\* Weak fairness on the memory's actions: every issued request is
\* eventually performed and answered.
Fairness == \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* A busy processor always holds a well-formed request in its buffer.
BusyHoldsRequest ==
    \A p \in Proc : ctl[p] = "busy" => buf[p] \in MReq

\* A processor whose request is done holds a valid reply.
DoneHoldsReply ==
    \A p \in Proc : ctl[p] = "done" => buf[p] \in ReplyVals

\* Memory semantics: a performed write is immediately visible in memory.
WriteTakesEffect ==
    [][\A p \in Proc :
          (Do(p) /\ buf[p].op = "Wr") => mem'[buf[p].adr] = buf[p].val]_vars

\* Memory semantics: a read returns the current contents of the location
\* and does not change memory.
ReadReturnsMemory ==
    [][\A p \in Proc :
          (Do(p) /\ buf[p].op = "Rd") =>
              /\ buf'[p] = mem[buf[p].adr]
              /\ mem' = mem]_vars

\* Every reply sent through the interface carries the value in the
\* processor's buffer.
ReplyMatchesBuffer ==
    [][\A p \in Proc : Rsp(p) => memInt' = <<p, buf[p]>>]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* Every request issued by a processor is eventually answered.
RequestEventuallyAnswered ==
    \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

\* Every processor is infinitely often ready to issue a new request.
ProcessorsProgress ==
    \A p \in Proc : []<>(ctl[p] = "rdy")

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => [](BusyHoldsRequest /\ DoneHoldsReply)
THEOREM Spec => WriteTakesEffect /\ ReadReturnsMemory /\ ReplyMatchesBuffer
THEOREM Spec => RequestEventuallyAnswered /\ ProcessorsProgress
=============================================================================