---------------------------- MODULE MCSession11projspec ----------------------------
(***************************************************************************)
(* Model-checking wrapper for an alternating-bit style protocol between   *)
(* processes A and B under an active environment that enqueues new        *)
(* values in NewValQueue.                                                  *)
(*                                                                         *)
(* The original wrapper EXTENDS Session11projspec. The underlying          *)
(* specification is inlined here so that the module is self-contained and *)
(* passes SANY. The wrapper part is below: the concrete data set, the     *)
(* state constraint on the length of NewValQueue, and the derived         *)
(* properties about AVar and BVar.                                        *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS Data,          \* set of data values that can be sent
          MaxQueueLen    \* bound on NewValQueue used by the state constraint

VARIABLES AVar,          \* <<value, bit>> currently held by A
          BVar,          \* <<value, bit>> last received by B
          NewValQueue    \* values proposed by the environment, not yet accepted by A

vars == <<AVar, BVar, NewValQueue>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Underlying specification (contents of Session11projspec)               *)
(***************************************************************************)

TypeOK ==
    /\ AVar \in Data \X {0, 1}
    /\ BVar \in Data \X {0, 1}
    /\ NewValQueue \in Seq(Data)

Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar
    /\ NewValQueue = << >>

\* The active environment proposes a new value.
EnvNewVal ==
    /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
    /\ UNCHANGED <<AVar, BVar>>

\* A accepts the next proposed value and flips its bit.
\* A does not wait for B, so its bit can alternate faster than B receives.
A ==
    /\ NewValQueue /= << >>
    /\ AVar' = << Head(NewValQueue), 1 - AVar[2] >>
    /\ NewValQueue' = Tail(NewValQueue)
    /\ UNCHANGED BVar

\* B receives A's current value.
B ==
    /\ AVar /= BVar
    /\ BVar' = AVar
    /\ UNCHANGED <<AVar, NewValQueue>>

Next == EnvNewVal \/ A \/ B

Fairness ==
    /\ WF_vars(A)
    /\ WF_vars(B)
    /\ WF_vars(EnvNewVal)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking wrapper                                                  *)
(***************************************************************************)

\* Concrete data set to substitute for the constant Data in the model.
MCData == {"d1", "d2"}

\* Concrete queue bound to substitute for MaxQueueLen in the model.
MCMaxQueueLen == 2

\* State constraint: limit the length of NewValQueue.
StateConstraint == Len(NewValQueue) =< MaxQueueLen

(***************************************************************************)
(* Safety-style predicates.                                                *)
(*                                                                         *)
(* An expected invariant is that equal bits imply equal states. It can    *)
(* fail: if the environment proposes new values too quickly and A accepts *)
(* them too quickly, A's bit can flip twice before B receives an update.  *)
(* The bits are then equal while the values differ.                       *)
(***************************************************************************)
ExpectedInv == (AVar[2] = BVar[2]) => (AVar = BVar)

\* Weaker predicate: whenever the states are equal, the bits are equal.
EqualImpliesSameBit == (AVar = BVar) => (AVar[2] = BVar[2])

\* B's value always comes from the data set.
BValueOK == BVar[1] \in Data

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* Infinitely often A and B agree.
InfOftenEqual == []<>(AVar = BVar)

\* Infinitely often A and B disagree.
InfOftenUnequal == []<>(AVar /= BVar)

\* Disagreement always leads to agreement.
Converge == (AVar /= BVar) ~> (AVar = BVar)

---------------------------------------------------------------------------
THEOREM Spec => []TypeOK
=============================================================================