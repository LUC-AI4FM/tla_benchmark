---------------------------- MODULE FingerprintNested ----------------------------
(***************************************************************************)
(* A small TLC-oriented test module for fingerprinting and state           *)
(* representation of nested function, set and record values.               *)
(* x ranges over functions from a singleton set to functions returning     *)
(* subsets of a base set.  y ranges over functions from a singleton set    *)
(* to functions returning subsets of records with fields a and b.          *)
(***************************************************************************)
EXTENDS Naturals, TLC

Dom  == {1}
Base == {"u", "v"}
Rec  == [a : {0, 1}, b : {0, 1}]

VARIABLES x, y

vars == <<x, y>>

(* Two type expressions for x and y, written in structurally different   *)
(* but semantically equivalent ways.                                       *)
XType1 == [Dom -> [Dom -> SUBSET Base]]
XType2 == [{1} -> [{1} -> SUBSET {"v", "u"}]]

YType1 == [Dom -> [Dom -> SUBSET Rec]]
YType2 == [{1} -> [{1} -> SUBSET [b : {1, 0}, a : {1, 0}]]]

TypeOK ==
    /\ x \in XType1
    /\ y \in YType1

Init ==
    /\ x = [i \in Dom |-> [j \in Dom |-> {}]]
    /\ y = [i \in Dom |-> [j \in Dom |-> {}]]

(* Invariant: the two equivalent type expressions must be equal;          *)
(* otherwise an assertion failure is triggered.                            *)
Inv ==
    /\ IF XType1 = XType2
          THEN TRUE
          ELSE Assert(FALSE, "XType1 and XType2 differ")
    /\ IF YType1 = YType2
          THEN TRUE
          ELSE Assert(FALSE, "YType1 and YType2 differ")
    /\ TypeOK

Stutter == UNCHANGED vars

SetX1 ==
    /\ x' = [x EXCEPT ![1][1] = {"u"}]
    /\ UNCHANGED y

SetX2 ==
    /\ x' = [x EXCEPT ![1][1] = @ \cup {"v"}]
    /\ UNCHANGED y

ResetX ==
    /\ x' = [i \in Dom |-> [j \in Dom |-> {}]]
    /\ UNCHANGED y

SetY1 ==
    /\ y' = [y EXCEPT ![1][1] = @ \cup {[a |-> 0, b |-> 1]}]
    /\ UNCHANGED x

SetY2 ==
    /\ y' = [y EXCEPT ![1] = [j \in Dom |-> {[b |-> 0, a |-> 1]}]]
    /\ UNCHANGED x

ResetY ==
    /\ y' = [i \in Dom |-> [j \in Dom |-> {}]]
    /\ UNCHANGED x

Next ==
    \/ Stutter
    \/ SetX1
    \/ SetX2
    \/ ResetX
    \/ SetY1
    \/ SetY2
    \/ ResetY

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Inv
==================================================================================