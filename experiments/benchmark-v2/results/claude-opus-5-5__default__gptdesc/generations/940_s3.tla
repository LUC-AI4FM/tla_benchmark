------------------------- MODULE MCLiveInternalMemory -------------------------
(***************************************************************************)
(* TLC support module for model checking LiveInternalMemory.  It gives    *)
(* concrete definitions for the constant operators Send, Reply and        *)
(* InitMemInt of the memory interface.  It also defines a liveness        *)
(* property saying every processor is busy infinitely often, and a        *)
(* PostCondition record describing a counterexample trace that violates   *)
(* that property.                                                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, Adr, Val

VARIABLES memInt, mem, ctl, buf

vars == <<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Memory interface (from MemoryInterface).                                *)
(***************************************************************************)
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete replacements for the constant operators Send, Reply and        *)
(* InitMemInt.                                                             *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

Send(p, d, oldMemInt, newMemInt)  == MCSend(p, d, oldMemInt, newMemInt)
Reply(p, d, oldMemInt, newMemInt) == MCReply(p, d, oldMemInt, newMemInt)
InitMemInt == MCInitMemInt

-----------------------------------------------------------------------------
(***************************************************************************)
(* Internal memory specification (InternalMemory).                         *)
(***************************************************************************)
Init ==
  /\ mem \in [Adr -> Val]
  /\ ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

TypeInvariant ==
  /\ mem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

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

ISpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Live internal memory (LiveInternalMemory).                              *)
(***************************************************************************)
Fairness == \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

Spec == ISpec /\ Fairness

LISpec == Spec

Liveness == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

(***************************************************************************)
(* Every processor is busy infinitely often.  This is not implied by Spec *)
(* because Req(p) is not fair.                                             *)
(***************************************************************************)
Liveness2 == \A p \in Proc : []<>(ctl[p] = "busy")

-----------------------------------------------------------------------------
(***************************************************************************)
(* PostCondition: a structured record describing a counterexample to      *)
(* Liveness2.  Processor p1 issues one write, completes it, and then the   *)
(* system stutters forever with every processor ready, so no processor is *)
(* ever busy again.                                                        *)
(***************************************************************************)
p1 == CHOOSE p \in Proc : TRUE
a1 == CHOOSE a \in Adr : TRUE
v1 == CHOOSE v \in Val : TRUE
v0 == CHOOSE v \in Val : TRUE

wreq == [op |-> "Wr", adr |-> a1, val |-> v1]

S1 == [memInt |-> <<p1, NoVal>>,
       mem    |-> [a \in Adr |-> v0],
       ctl    |-> [p \in Proc |-> "rdy"],
       buf    |-> [p \in Proc |-> NoVal]]

S2 == [memInt |-> <<p1, wreq>>,
       mem    |-> [a \in Adr |-> v0],
       ctl    |-> [p \in Proc |-> IF p = p1 THEN "busy" ELSE "rdy"],
       buf    |-> [p \in Proc |-> IF p = p1 THEN wreq ELSE NoVal]]

S3 == [memInt |-> <<p1, wreq>>,
       mem    |-> [a \in Adr |-> IF a = a1 THEN v1 ELSE v0],
       ctl    |-> [p \in Proc |-> IF p = p1 THEN "done" ELSE "rdy"],
       buf    |-> [p \in Proc |-> NoVal]]

S4 == [memInt |-> <<p1, NoVal>>,
       mem    |-> [a \in Adr |-> IF a = a1 THEN v1 ELSE v0],
       ctl    |-> [p \in Proc |-> "rdy"],
       buf    |-> [p \in Proc |-> NoVal]]

PostCondition ==
  [property |-> "Liveness2",
   kind     |-> "temporal",
   trace    |-> << [position |-> 1, action |-> [name |-> "Init"],
                    state |-> S1],
                   [position |-> 2, action |-> [name |-> "Req", proc |-> p1],
                    state |-> S2],
                   [position |-> 3, action |-> [name |-> "Do", proc |-> p1],
                    state |-> S3],
                   [position |-> 4, action |-> [name |-> "Rsp", proc |-> p1],
                    state |-> S4],
                   [position |-> 5, action |-> [name |-> "Stuttering"],
                    state |-> S4] >>,
   loopsBackTo |-> 4]

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => Liveness
=============================================================================