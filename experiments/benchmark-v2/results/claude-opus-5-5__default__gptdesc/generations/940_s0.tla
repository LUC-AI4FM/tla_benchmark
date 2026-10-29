------------------------- MODULE MCLiveInternalMemory -------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc, Adr, Val

VARIABLES memInt, mem, ctl, buf

vars == <<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Memory interface definitions                                            *)
(***************************************************************************)
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete replacements for the constant operators Send, Reply and       *)
(* InitMemInt, so that TLC can evaluate the transitions.                   *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

Send(p, d, oldMemInt, newMemInt)  == MCSend(p, d, oldMemInt, newMemInt)
Reply(p, d, oldMemInt, newMemInt) == MCReply(p, d, oldMemInt, newMemInt)
InitMemInt == MCInitMemInt

-----------------------------------------------------------------------------
(***************************************************************************)
(* Internal memory specification                                           *)
(***************************************************************************)
TypeInvariant ==
  /\ mem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

Init ==
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

Next == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
Liveness == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

\* Every processor is busy infinitely often (expected to fail under Spec,
\* since a processor is never forced to issue a request).
Liveness2 == \A p \in Proc : []<>(ctl[p] = "busy")

THEOREM Spec => []TypeInvariant
THEOREM Spec => Liveness

-----------------------------------------------------------------------------
(***************************************************************************)
(* PostCondition: a structured record describing a specific counterexample *)
(* trace for Liveness2, consisting of action and state snapshots.          *)
(***************************************************************************)
PostCondition ==
  [ property |-> "Liveness2",
    kind     |-> "counterexample",
    lassoStart |-> 1,
    trace |->
      << [ action |-> [ name |-> "Initial predicate", proc |-> "none" ],
           state  |-> [ memInt |-> <<"p1", "NoVal">>,
                        mem    |-> [ a1 |-> "v1" ],
                        ctl    |-> [ p1 |-> "rdy", p2 |-> "rdy" ],
                        buf    |-> [ p1 |-> "NoVal", p2 |-> "NoVal" ] ] ],
         [ action |-> [ name |-> "Req", proc |-> "p1" ],
           state  |-> [ memInt |-> <<"p1", [op |-> "Rd", adr |-> "a1"]>>,
                        mem    |-> [ a1 |-> "v1" ],
                        ctl    |-> [ p1 |-> "busy", p2 |-> "rdy" ],
                        buf    |-> [ p1 |-> [op |-> "Rd", adr |-> "a1"],
                                     p2 |-> "NoVal" ] ] ],
         [ action |-> [ name |-> "Do", proc |-> "p1" ],
           state  |-> [ memInt |-> <<"p1", [op |-> "Rd", adr |-> "a1"]>>,
                        mem    |-> [ a1 |-> "v1" ],
                        ctl    |-> [ p1 |-> "done", p2 |-> "rdy" ],
                        buf    |-> [ p1 |-> "v1", p2 |-> "NoVal" ] ] ],
         [ action |-> [ name |-> "Rsp", proc |-> "p1" ],
           state  |-> [ memInt |-> <<"p1", "v1">>,
                        mem    |-> [ a1 |-> "v1" ],
                        ctl    |-> [ p1 |-> "rdy", p2 |-> "rdy" ],
                        buf    |-> [ p1 |-> "v1", p2 |-> "NoVal" ] ] ],
         [ action |-> [ name |-> "Stuttering", proc |-> "none" ],
           state  |-> [ memInt |-> <<"p1", "v1">>,
                        mem    |-> [ a1 |-> "v1" ],
                        ctl    |-> [ p1 |-> "rdy", p2 |-> "rdy" ],
                        buf    |-> [ p1 |-> "v1", p2 |-> "NoVal" ] ] ]
      >> ]

=============================================================================