---------------------------- MODULE MCSession11projspec ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the Session 11 project specification.        *)
(* The original wrapper uses EXTENDS Session11projspec. To keep this file   *)
(* self-contained and parseable by SANY, the underlying alternating-bit     *)
(* style specification is included inline.                                  *)
(*                                                                          *)
(* Process A holds AVar = <<value, bit>> and process B holds BVar.          *)
(* An active environment enqueues new values onto NewValQueue. A takes the  *)
(* head of the queue and flips its bit. B copies AVar whenever the two      *)
(* differ.                                                                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES AVar, BVar, NewValQueue

vars == <<AVar, BVar, NewValQueue>>

(***************************************************************************)
(* Concrete constant data set substituted for Data in the model.            *)
(***************************************************************************)
ConstData == {"d1", "d2"}

(***************************************************************************)
(* State constraint that bounds the length of NewValQueue.                  *)
(***************************************************************************)
MaxQueueLen == 2
StateConstraint == Len(NewValQueue) <= MaxQueueLen

-----------------------------------------------------------------------------
(* Underlying specification *)

TypeOK ==
    /\ AVar \in Data \X {0, 1}
    /\ BVar \in Data \X {0, 1}
    /\ NewValQueue \in Seq(Data)

Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar
    /\ NewValQueue = << >>

(* The active environment proposes a new value. *)
EnvPropose ==
    /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
    /\ UNCHANGED <<AVar, BVar>>

(* A accepts the next proposed value and flips its bit. A does not wait     *)
(* for B, so its bit can alternate faster than B receives updates.          *)
A ==
    /\ NewValQueue /= << >>
    /\ AVar' = <<Head(NewValQueue), 1 - AVar[2]>>
    /\ NewValQueue' = Tail(NewValQueue)
    /\ UNCHANGED BVar

(* B receives A's current value when the two disagree. *)
B ==
    /\ AVar /= BVar
    /\ BVar' = AVar
    /\ UNCHANGED <<AVar, NewValQueue>>

Next == EnvPropose \/ A \/ B

Fairness == WF_vars(B)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Derived properties about the relationship between AVar and BVar *)

(***************************************************************************)
(* Previously expected invariant: if the bits agree then the values agree. *)
(* It may FAIL: when the environment proposes new values too quickly and A  *)
(* accepts them too quickly, A's bit can alternate twice before B receives  *)
(* an update, so the bits agree while the values differ.                    *)
(***************************************************************************)
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

(* Safety-style predicates for examination. *)
Equal   == AVar = BVar
Unequal == AVar /= BVar
BitsDiffer == AVar[2] /= BVar[2]
SafetyPred == Equal \/ BitsDiffer

(* Liveness properties. *)
RecurEqual   == []<>(AVar = BVar)
RecurUnequal == []<>(AVar /= BVar)
Converge     == (AVar /= BVar) ~> (AVar = BVar)

THEOREM Spec => []TypeOK
THEOREM Spec => Converge
=============================================================================