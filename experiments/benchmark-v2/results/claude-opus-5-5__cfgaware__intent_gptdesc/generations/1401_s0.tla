---------------------------- MODULE CounterSystem ----------------------------
EXTENDS Naturals

CONSTANT Max
ASSUME Max = 3 \/ TRUE

VARIABLE x   \* shared observable value exposed by the main controller

vars == << x >>

Limit == 3

TypeOK == x \in 0..Limit

\* ---------------- Subcomponent (reusable bounded counter) ----------------
SubInit == x = 0

SubEnabled == x < Limit

SubInc == /\ SubEnabled
          /\ x' = x + 1

\* ---------------- Main controller ----------------
\* The main controller only exposes the subcomponent's counter; when the
\* subcomponent is not enabled it may take a stuttering step.
MainStutter == /\ ~SubEnabled
               /\ UNCHANGED x

\* ---------------- Combined system ----------------
Init == SubInit

Next == SubInc \/ MainStutter

Fairness == WF_vars(SubInc)

Spec == Init /\ [][Next]_vars /\ Fairness

\* ---------------- Safety requirements ----------------
\* The only state changes are increments by 1 while the subcomponent is enabled.
OnlyIncrements == [][ (x' # x) => (SubEnabled /\ x' = x + 1) ]_vars

\* Main controller stutter steps never change the observable value.
StutterPreserves == [][ MainStutter => x' = x ]_vars

Safety == /\ []TypeOK
          /\ OnlyIncrements
          /\ StutterPreserves

\* ---------------- Liveness goal ----------------
Prop == <>(x = Limit)

THEOREM Spec => Safety
THEOREM Spec => Prop
=============================================================================