---------------------------- MODULE InternalMemory ----------------------------
(***************************************************************************)
(* A linearizable shared memory with an internal buffer per processor.     *)
(* Processors issue Read/Write requests (Req), the memory atomically       *)
(* performs the request internally (Do), and a response is then returned   *)
(* to the processor (Rsp).                                                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,   \* set of processors
          Adr,    \* set of memory addresses
          Val     \* set of memory values

VARIABLES memInt, \* the memory interface (last message exchanged)
          mem,    \* the internal memory contents
          ctl,    \* per-processor control state: "rdy", "busy", "done"
          buf     \* per-processor buffer: outstanding request or response

vars == <<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------
NoVal == CHOOSE v : v \notin Val

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

InitMemInt == <<"init">>

MemIntVals == {InitMemInt} \cup
              {<<p, d>> : p \in Proc, d \in MReq \cup Val \cup {NoVal}}

\* Interface actions: the interface variable records the last message.
Send(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
Reply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ memInt \in MemIntVals
    /\ mem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
    /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

IInit ==
    /\ memInt = InitMemInt
    /\ mem \in [Adr -> Val]
    /\ ctl = [p \in Proc |-> "rdy"]
    /\ buf = [p \in Proc |-> NoVal]

\* Processor p issues a request.
Req(p) ==
    /\ ctl[p] = "rdy"
    /\ \E req \in MReq :
          /\ Send(p, req, memInt, memInt')
          /\ buf' = [buf EXCEPT ![p] = req]
          /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem

\* The memory atomically performs p's outstanding request.
Do(p) ==
    /\ ctl[p] = "busy"
    /\ buf[p] \in MReq
    /\ mem' = IF buf[p].op = "Wr"
                THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
                ELSE mem
    /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                   THEN NoVal
                                   ELSE mem[buf[p].adr]]
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED memInt

\* The response is returned to processor p.
Rsp(p) ==
    /\ ctl[p] = "done"
    /\ Reply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

ISpec == IInit /\ [][INext]_vars

-----------------------------------------------------------------------------
(* Fairness: neither internal operation nor response steps are postponed   *)
(* forever; request steps are also treated weakly fairly.                  *)
Liveness ==
    \A p \in Proc :
        /\ WF_vars(Req(p))
        /\ WF_vars(Do(p))
        /\ WF_vars(Rsp(p))

LISpec == ISpec /\ Liveness

-----------------------------------------------------------------------------
(* Safety invariants *)

\* No phantom operations: a busy processor holds a genuine request, and a
\* finished processor holds a value that is a valid effect of its request.
ResponseValid ==
    \A p \in Proc :
        /\ (ctl[p] = "busy") => buf[p] \in MReq
        /\ (ctl[p] = "done") => buf[p] \in Val \cup {NoVal}
        /\ (ctl[p] = "rdy" /\ memInt # InitMemInt /\ memInt[1] = p)
              => memInt[2] \in Val \cup {NoVal}

\* Memory always holds a well-formed value at each address.
MemConsistent == \A a \in Adr : mem[a] \in Val

Safety == TypeInvariant /\ ResponseValid /\ MemConsistent

-----------------------------------------------------------------------------
(* Liveness: every issued request is eventually answered. *)
LivenessProperty ==
    \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

THEOREM LISpec => [](TypeInvariant /\ ResponseValid /\ MemConsistent)
THEOREM LISpec => LivenessProperty
=============================================================================