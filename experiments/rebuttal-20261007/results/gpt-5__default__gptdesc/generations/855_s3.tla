------------------------------ MODULE PrisonersSwitches ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  P,          \* Set of prisoners (finite, nonempty)
  Counter     \* Designated counter, an element of P

ASSUME Counter \in P

\* Variables:
\* A, B       : booleans for switches A and B (TRUE = up, FALSE = down)
\* allowedA   : function P -> {0,1,2} tracking how many times each non-counter raised A
\* visited    : set of prisoners who have visited the room at least once
\* count      : counter's tally of times he found A up and turned it down
\* declared   : TRUE once the counter declares completion
VARIABLES A, B, allowedA, visited, count, declared

Others == P \ {Counter}
Goal == 2 * Cardinality(Others)

Init ==
  /\ A = FALSE
  /\ B = FALSE
  /\ allowedA = [p \in P |-> 0]
  /\ visited = {}
  /\ count = 0
  /\ declared = FALSE

Step(p) ==
  /\ p \in P
  /\ IF declared
        THEN UNCHANGED <<A, B, allowedA, visited, count, declared>>
        ELSE
          /\ visited' = visited \cup {p}
          /\ IF p = Counter THEN
                CASE A ->
                       /\ A' = FALSE
                       /\ count' = count + 1
                       /\ declared' = (count + 1) = Goal
                       /\ UNCHANGED <<B, allowedA>>
                   [] ~A ->
                       /\ B' = ~B
                       /\ UNCHANGED <<A, allowedA, count>>
                       /\ declared' = (count = Goal)
             ELSE
                CASE (~A /\ allowedA[p] < 2) ->
                       /\ A' = TRUE
                       /\ allowedA' = [allowedA EXCEPT ![p] = @ + 1]
                       /\ UNCHANGED <<B, count>>
                       /\ declared' = declared
                   [] OTHER ->
                       /\ B' = ~B
                       /\ UNCHANGED <<A, allowedA, count>>
                       /\ declared' = declared

Next == \E p \in P: Step(p)

vars == <<A, B, allowedA, visited, count, declared>>

\* Weak fairness: each prisoner is brought into the room infinitely often.
Fairness == \A p \in P: WF_vars(Step(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: when the protocol declares completion, every prisoner has visited.
SafetyInvariant == [](declared => visited = P)

\* Liveness: the declaration condition is eventually reached.
Termination == <>declared

=============================================================================