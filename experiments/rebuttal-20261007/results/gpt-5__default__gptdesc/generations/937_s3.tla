------------------------------ MODULE LiveHourClock ------------------------------

EXTENDS Integers

CONSTANTS MinHour, MaxHour

ASSUME /\ MinHour = 1
       /\ MaxHour = 12
       /\ MinHour < MaxHour

VARIABLES hr

Hours == MinHour .. MaxHour

Init ==
  hr \in Hours

HCnxt ==
  hr' = IF hr < MaxHour THEN hr + 1 ELSE MinHour

HC ==
  Init /\ [][HCnxt]_hr

\* Liveness-augmented specification: inherited clock spec conjoined with weak fairness on hr.
LSpec ==
  HC /\ WF_hr(HCnxt)

\* For convenience, expose standard names required by the task.
Next == HCnxt
Spec == LSpec

\* Safety invariants
TypeInv == hr \in Hours
AlwaysType == []TypeInv

\* Liveness properties
TickInfOften == []<>HCnxt

HrsInfOften == \A h \in Hours: []<>(hr = h)

\* A settling property (eventual stabilization) and a concrete counterexample-shaped postcondition.
Settles ==
  <>[](\E h \in Hours: hr = h)

\* A concrete counterexample structure to Settles: all hour values recur infinitely often.
CEPost ==
  /\ ~Settles
  /\ HrsInfOften

\* Theorems asserted from the liveness-augmented spec.
THEOREM LSpec => TickInfOften /\ HrsInfOften /\ AlwaysType

THEOREM LSpec => ~Settles

=============================================================================