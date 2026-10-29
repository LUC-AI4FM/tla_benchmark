-------------------------------- MODULE ABSpec --------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar,        \* <<value, bit>> currently being sent by A
          BVar,        \* <<value, bit>> last value received by B
          NewValQueue  \* queue of pending data values to be sent

vars == << AVar, BVar, NewValQueue >>

TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ NewValQueue \in Seq(Data)

-----------------------------------------------------------------------------

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ NewValQueue = << >>

(* A takes the next pending value from the queue and flips the bit,       *)
(* but only after B has received the previous value.                      *)
A == /\ AVar = BVar
     /\ NewValQueue # << >>
     /\ AVar' = << Head(NewValQueue), 1 - AVar[2] >>
     /\ NewValQueue' = Tail(NewValQueue)
     /\ BVar' = BVar

(* B copies A's value when the alternating bit has changed.               *)
B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ UNCHANGED << AVar, NewValQueue >>

(* The environment E nondeterministically appends a new data value.       *)
E == /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
     /\ UNCHANGED << AVar, BVar >>

Next == A \/ B \/ E

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)

-----------------------------------------------------------------------------
(* Safety: B only ever holds a value that A sent; values differ only when *)
(* the bits differ.                                                        *)
Consistent == (AVar[2] = BVar[2]) => (AVar = BVar)

(* Liveness: every value sent by A is eventually received by B.           *)
Delivery == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

(* Liveness: whenever there are pending values, A eventually sends one.   *)
Progress == (NewValQueue # << >>) ~> (AVar # BVar)

THEOREM Spec => [](TypeOK /\ Consistent)
THEOREM Spec => Delivery
=============================================================================