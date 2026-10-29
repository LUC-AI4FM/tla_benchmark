------------------------- MODULE MCLiveInternalMemory -------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc, Adr, Val, NoVal

ASSUME NoVal \notin Val

VARIABLES mem, ctl, buf, memInt

vars == <<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------
(* Concrete replacements for the constant operators of InternalMemory     *)
-----------------------------------------------------------------------------

MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

Send(p, d, oldMemInt, newMemInt)  == MCSend(p, d, oldMemInt, newMemInt)
Reply(p, d, oldMemInt, newMemInt) == MCReply(p, d, oldMemInt, newMemInt)
InitMemInt == MCInitMemInt

-----------------------------------------------------------------------------
(* The internal memory specification                                       *)
-----------------------------------------------------------------------------

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

Init == IInit

Next == INext

ISpec == IInit /\ [][INext]_vars

Liveness == \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

LISpec == ISpec /\ Liveness

Spec == LISpec

-----------------------------------------------------------------------------
(* Liveness formula: every processor is busy infinitely often             *)
-----------------------------------------------------------------------------

Liveness2 == \A p \in Proc : []<>(ctl[p] = "busy")

-----------------------------------------------------------------------------
(* Structured description of a specific counterexample trace              *)
-----------------------------------------------------------------------------

PostCondition ==
  [ kind        |-> "counterexample",
    property    |-> "Liveness2",
    loopsAtStep |-> 2,
    trace       |->
      << [ action |-> [ name |-> "Initial predicate", proc |-> "none" ],
           state  |-> [ mem    |-> "a1 :> v1",
                        ctl    |-> << "rdy", "rdy" >>,
                        buf    |-> << "NoVal", "NoVal" >>,
                        memInt |-> << "p1", "NoVal" >> ] ],
         [ action |-> [ name |-> "Req", proc |-> "p1" ],
           state  |-> [ mem    |-> "a1 :> v1",
                        ctl    |-> << "busy", "rdy" >>,
                        buf    |-> << [op |-> "Rd", adr |-> "a1"], "NoVal" >>,
                        memInt |-> << "p1", [op |-> "Rd", adr |-> "a1"] >> ] ],
         [ action |-> [ name |-> "Do", proc |-> "p1" ],
           state  |-> [ mem    |-> "a1 :> v1",
                        ctl    |-> << "done", "rdy" >>,
                        buf    |-> << "v1", "NoVal" >>,
                        memInt |-> << "p1", [op |-> "Rd", adr |-> "a1"] >> ] ],
         [ action |-> [ name |-> "Rsp", proc |-> "p1" ],
           state  |-> [ mem    |-> "a1 :> v1",
                        ctl    |-> << "rdy", "rdy" >>,
                        buf    |-> << "v1", "NoVal" >>,
                        memInt |-> << "p1", "v1" >> ] ],
         [ action |-> [ name |-> "Req", proc |-> "p1" ],
           state  |-> [ mem    |-> "a1 :> v1",
                        ctl    |-> << "busy", "rdy" >>,
                        buf    |-> << [op |-> "Rd", adr |-> "a1"], "NoVal" >>,
                        memInt |-> << "p1", [op |-> "Rd", adr |-> "a1"] >> ] ]
      >> ]

=============================================================================