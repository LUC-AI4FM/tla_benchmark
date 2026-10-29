--------------------------- MODULE ABSpec ---------------------------
(***************************************************************************)
(* Abstract specification of what the Alternating Bit protocol is meant   *)
(* to accomplish.                                                         *)
(*                                                                         *)
(* A: takes the next pending value from NewValQueue, makes it the current *)
(*    message, and flips the bit.                                          *)
(* B: copies A's value when the alternating bit changes.                   *)
(* E: nondeterministically appends a new value from Data to the queue.    *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, NewValQueue

vars == << AVar, BVar, NewValQueue >>

TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ NewValQueue \in Seq(Data)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ NewValQueue = << >>

A == /\ AVar = BVar
     /\ NewValQueue # << >>
     /\ AVar' = << Head(NewValQueue), 1 - AVar[2] >>
     /\ NewValQueue' = Tail(NewValQueue)
     /\ BVar' = BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ UNCHANGED << AVar, NewValQueue >>

E == /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
     /\ UNCHANGED << AVar, BVar >>

Next == A \/ B \/ E

Spec == Init /\ [][Next]_vars /\ WF_vars(A) /\ WF_vars(B)

-----------------------------------------------------------------------------
(* Safety invariants *)

(* Whenever the bits agree, B holds exactly A's current value. *)
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

(* B is either synchronized with A or exactly one step behind it. *)
SyncInv == \/ BVar = AVar
           \/ BVar[2] = 1 - AVar[2]

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Every value A sends is eventually received by B. *)
Delivery == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

(* Whenever a value is pending in the queue, A eventually sends again. *)
Progress == (NewValQueue # << >>) ~> (AVar = BVar)

THEOREM Spec => [](TypeOK /\ Inv /\ SyncInv)
THEOREM Spec => Delivery
=============================================================================