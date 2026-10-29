------------------------------- MODULE LockHS -------------------------------
EXTENDS Integers

Proc == {0, 1}

(***************************************************************************)
(* Peterson's algorithm, written as an inner module so it can be           *)
(* instantiated below. Each process p does three steps to enter:           *)
(*   a1: set flag[p]                                                       *)
(*   a2: give the turn to the other process                                *)
(*   a3: wait until the other is not interested or it is p's turn          *)
(***************************************************************************)
------------------------------ MODULE Peterson ------------------------------
VARIABLES pc, flag, turn

vars == <<pc, flag, turn>>

TypeOK ==
  /\ pc \in [Proc -> {"a1", "a2", "a3", "cs"}]
  /\ flag \in [Proc -> BOOLEAN]
  /\ turn \in Proc

Init ==
  /\ pc = [p \in Proc |-> "a1"]
  /\ flag = [p \in Proc |-> FALSE]
  /\ turn \in Proc

A1(p) ==
  /\ pc[p] = "a1"
  /\ flag' = [flag EXCEPT ![p] = TRUE]
  /\ pc' = [pc EXCEPT ![p] = "a2"]
  /\ UNCHANGED turn

A2(p) ==
  /\ pc[p] = "a2"
  /\ turn' = 1 - p
  /\ pc' = [pc EXCEPT ![p] = "a3"]
  /\ UNCHANGED flag

A3(p) ==
  /\ pc[p] = "a3"
  /\ (~flag[1 - p] \/ turn = p)
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<flag, turn>>

CS(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "a1"]
  /\ flag' = [flag EXCEPT ![p] = FALSE]
  /\ UNCHANGED turn

Next == \E p \in Proc : A1(p) \/ A2(p) \/ A3(p) \/ CS(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")
=============================================================================