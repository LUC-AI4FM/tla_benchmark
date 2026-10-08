------------------------------ MODULE PrisonersAndSwitches ------------------------------
EXTENDS Naturals

CONSTANTS N, COUNTER
P == 1..N
c == COUNTER

VARIABLES A, visited, upsUsed, counterCount

vars == <<A, visited, upsUsed, counterCount>>

Init ==
   /\ A = FALSE
   /\ counterCount = 0
   /\ visited = [i \in P |-> FALSE]
   /\ upsUsed = [i \in P |-> 0]

Action(p) ==
   IF p = c THEN
      /\ A' = IF A THEN FALSE ELSE A
      /\ counterCount' = IF A THEN counterCount + 1 ELSE counterCount
      /\ visited' = [visited EXCEPT ![c] = TRUE]
   ELSE
      /\ visited' = [visited EXCEPT ![p] = TRUE]
      /\ IF (A = FALSE) ∧ (upsUsed[p] < 2) THEN
            /\ A' = TRUE
            /\ upsUsed' = [upsUsed EXCEPT ![p] = upsUsed[p]+1]
         ELSE
            /\ A' = A
            /\ upsUsed' = upsUsed
        ENDIF

Next == ∃p \in P : Action(p)

CompletionDeclared == counterCount = 2 * (N - 1)
SafetyInvariant ==
   CompletionDeclared => (\A p \in P : visited[p])

Fairness == ∧ p \in P : WF_Action(Action(p))

Spec == Init /\ [][Next]_vars /\ Fairness

THEOREM SafetyTheorem == Spec => []SafetyInvariant
THEOREM LivenessTheorem == Spec => <> CompletionDeclared
======================================================================================