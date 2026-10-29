---------------------------- MODULE MCLiveInternal ----------------------------
(***************************************************************************)
(* TLC support module for model checking LiveInternalMemory.               *)
(* It is self-contained: the MemoryInterface, InternalMemory and           *)
(* LiveInternalMemory definitions are inlined. The constant operators      *)
(* Send, Reply and InitMemInt are replaced by the concrete operators       *)
(* MCSend, MCReply and MCInitMemInt so that TLC can evaluate them.         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, Adr, Val

VARIABLES memInt, mem, ctl, buf

vars == <<memInt, mem, ctl, buf>>

(***************************************************************************)
(* MemoryInterface definitions                                             *)
(***************************************************************************)
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

(***************************************************************************)
(* Concrete replacements for the constant operators                        *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

Send(p, d, oldMemInt, newMemInt)  == MCSend(p, d, oldMemInt, newMemInt)
Reply(p, d, oldMemInt, newMemInt) == MCReply(p, d, oldMemInt, newMemInt)
InitMemInt == MCInitMemInt

(***************************************************************************)
(* InternalMemory definitions                                              *)
(***************************************************************************)
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

(***************************************************************************)
(* LiveInternalMemory definitions                                          *)
(***************************************************************************)
Liveness == \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

LISpec == ISpec /\ Liveness

Init == IInit
Next == INext
Spec == LISpec

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
\* Every request that is being processed is eventually answered.
BusyLeadsToRdy == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

\* Every processor is busy infinitely often (not implied by Spec; TLC
\* produces a counterexample, described by PostCondition below).
Liveness2 == \A p \in Proc : []<>(ctl[p] = "busy")

THEOREM Spec => []TypeInvariant

(***************************************************************************)
(* PostCondition: a structured description of a counterexample trace to    *)
(* Liveness2, as a sequence of action and state snapshots. The trace ends  *)
(* in a stuttering loop in which some processor is never again busy.       *)
(***************************************************************************)
PostCondition ==
  [ property |-> "Liveness2",
    loopsAt  |-> 7,
    trace    |->
      << [ action |-> [name |-> "Initial predicate", proc |-> "none"],
           state  |-> [ memInt |-> <<"p1", "NoVal">>,
                        mem    |-> [a1 |-> "v1"],
                        ctl    |-> [p1 |-> "rdy",  p2 |-> "rdy"],
                        buf    |-> [p1 |-> "NoVal", p2 |-> "NoVal"] ] ],
         [ action |-> [name |-> "Req", proc |-> "p1"],
           state  |-> [ memInt |-> <<"p1", [op |-> "Wr", adr |-> "a1", val |-> "v2"]>>,
                        mem    |-> [a1 |-> "v1"],
                        ctl    |-> [p1 |-> "busy", p2 |-> "rdy"],
                        buf    |-> [p1 |-> [op |-> "Wr", adr |-> "a1", val |-> "v2"],
                                    p2 |-> "NoVal"] ] ],
         [ action |-> [name |-> "Do", proc |-> "p1"],
           state  |-> [ memInt |-> <<"p1", [op |-> "Wr", adr |-> "a1", val |-> "v2"]>>,
                        mem    |-> [a1 |-> "v2"],
                        ctl    |-> [p1 |-> "done", p2 |-> "rdy"],
                        buf    |-> [p1 |-> "NoVal", p2 |-> "NoVal"] ] ],
         [ action |-> [name |-> "Rsp", proc |-> "p1"],
           state  |-> [ memInt |-> <<"p1", "NoVal">>,
                        mem    |-> [a1 |-> "v2"],
                        ctl    |-> [p1 |-> "rdy",  p2 |-> "rdy"],
                        buf    |-> [p1 |-> "NoVal", p2 |-> "NoVal"] ] ],
         [ action |-> [name |-> "Req", proc |-> "p1"],
           state  |-> [ memInt |-> <<"p1", [op |-> "Rd", adr |-> "a1"]>>,
                        mem    |-> [a1 |-> "v2"],
                        ctl    |-> [p1 |-> "busy", p2 |-> "rdy"],
                        buf    |-> [p1 |-> [op |-> "Rd", adr |-> "a1"],
                                    p2 |-> "NoVal"] ] ],
         [ action |-> [name |-> "Do", proc |-> "p1"],
           state  |-> [ memInt |-> <<"p1", [op |-> "Rd", adr |-> "a1"]>>,
                        mem    |-> [a1 |-> "v2"],
                        ctl    |-> [p1 |-> "done", p2 |-> "rdy"],
                        buf    |-> [p1 |-> "v2", p2 |-> "NoVal"] ] ],
         [ action |-> [name |-> "Rsp", proc |-> "p1"],
           state  |-> [ memInt |-> <<"p1", "v2">>,
                        mem    |-> [a1 |-> "v2"],
                        ctl    |-> [p1 |-> "rdy",  p2 |-> "rdy"],
                        buf    |-> [p1 |-> "v2", p2 |-> "NoVal"] ] ],
         [ action |-> [name |-> "Stuttering", proc |-> "none"],
           state  |-> [ memInt |-> <<"p1", "v2">>,
                        mem    |-> [a1 |-> "v2"],
                        ctl    |-> [p1 |-> "rdy",  p2 |-> "rdy"],
                        buf    |-> [p1 |-> "v2", p2 |-> "NoVal"] ] ]
      >> ]

PostConditionWellFormed ==
  /\ Len(PostCondition.trace) = 8
  /\ PostCondition.loopsAt \in 1..Len(PostCondition.trace)
=============================================================================