---- MODULE Session11projMC ----
(***************************************************************************)
(* Model-checking wrapper for an alternating-bit style protocol between    *)
(* processes A and B, running under an active environment that may        *)
(* enqueue new values onto NewValQueue.                                    *)
(*                                                                         *)
(* The original wrapper EXTENDS Session11projspec. That module is not      *)
(* available, so its content is inlined below. This keeps the module       *)
(* self-contained and parseable by SANY.                                   *)
(*                                                                         *)
(* NOTE: an invariant one might expect, such as "A and B differ by at most *)
(* one value", can FAIL. If the environment proposes new values too        *)
(* quickly and A accepts them too quickly, A's bit can alternate faster    *)
(* than B receives updates. For that reason we check both safety-style     *)
(* predicates and liveness properties: recurrence of equal and unequal     *)
(* states, and eventual convergence from disagreement to agreement.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC

CONSTANTS Data, MaxQueueLen

ASSUME Data # {} /\ MaxQueueLen \in Nat

VARIABLES AVar, BVar, NewValQueue

vars == <<AVar, BVar, NewValQueue>>

(* Concrete constant data set used when model checking.                    *)
MCData == {"d1", "d2"}

TypeOK ==
  /\ AVar \in Data \X {0, 1}
  /\ BVar \in Data \X {0, 1}
  /\ NewValQueue \in Seq(Data)

Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ NewValQueue = << >>

(* The environment proposes a new value.                                   *)
EnvPropose ==
  /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
  /\ UNCHANGED <<AVar, BVar>>

(* A accepts a new value and flips its bit.                                *)
(* A does not wait for B, so it may run ahead of B.                        *)
A ==
  /\ NewValQueue # << >>
  /\ AVar' = <<Head(NewValQueue), 1 - AVar[2]>>
  /\ NewValQueue' = Tail(NewValQueue)
  /\ UNCHANGED BVar

(* B receives A's current value when the two differ.                       *)
B ==
  /\ AVar # BVar
  /\ BVar' = AVar
  /\ UNCHANGED <<AVar, NewValQueue>>

Next == EnvPropose \/ A \/ B

Spec == Init /\ [][Next]_vars /\ WF_vars(A) /\ WF_vars(B)

(* State constraint: limit the length of NewValQueue.                      *)
StateConstraint == Len(NewValQueue) <= MaxQueueLen

(***************************************************************************)
(* Derived properties about the relationship between AVar and BVar.        *)
(***************************************************************************)

(* Expected invariant: equal bits imply equal values. This may FAIL,       *)
(* because A can flip its bit twice before B catches up.                   *)
BitsAgreeImpliesEqual == (AVar[2] = BVar[2]) => (AVar = BVar)

(* Weaker predicate: equal values agree on the bit.                        *)
ValueAgreement == (AVar = BVar) => (AVar[2] = BVar[2])

(* Safety-style predicate: A and B either agree or differ.                 *)
EqualOrUnequal == (AVar = BVar) \/ (AVar # BVar)

(* Liveness: equal states recur infinitely often.                          *)
RecurEqual == []<>(AVar = BVar)

(* Liveness: unequal states recur infinitely often.                        *)
(* This may fail if the environment stops proposing values.                *)
RecurUnequal == []<>(AVar # BVar)

(* Liveness: disagreement eventually leads to agreement.                   *)
Converges == (AVar # BVar) ~> (AVar = BVar)

THEOREM Spec => [](TypeOK /\ ValueAgreement)
====