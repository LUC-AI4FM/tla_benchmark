-------------------------- MODULE PrisonersAndSwitches --------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Prisoner

ASSUME IsFiniteSet(Prisoner) /\ Cardinality(Prisoner) > 1

VARIABLES p2, p3

vars == <<p2, p3>>

Counter == CHOOSE p \in Prisoner : TRUE
NonCounter == Prisoner \ {Counter}
NumPrisoners == Cardinality(Prisoner)
DoneCount == 2 * (NumPrisoners - 1)

TypeOK ==
    /\ p2 \in [ switchA  : BOOLEAN,
                switchB  : BOOLEAN,
                count    : 0..DoneCount,
                turnedUp : [NonCounter -> 0..2],
                declared : BOOLEAN ]
    /\ p3 \subseteq Prisoner

Init ==
    /\ p2 = [ switchA  |-> FALSE,
              switchB  |-> FALSE,
              count    |-> 0,
              turnedUp |-> [p \in NonCounter |-> 0],
              declared |-> FALSE ]
    /\ p3 = {}

CounterVisit ==
    /\ p2.declared = FALSE
    /\ IF p2.switchA THEN
          LET new_count == p2.count + 1 IN
          /\ p2' = [p2 EXCEPT !.count = new_count,
                               !.switchA = FALSE,
                               !.declared = (new_count = DoneCount)]
       ELSE
          /\ p2' = [p2 EXCEPT !.switchB = \lnot @]
    /\ p3' = p3 \cup {Counter}

NonCounterVisit(p) ==
    /\ p \in NonCounter
    /\ p2.declared = FALSE
    /\ IF \lnot p2.switchA /\ p2.turnedUp[p] < 2 THEN
          /\ p2' = [p2 EXCEPT !.switchA = TRUE, !.turnedUp[p] = @ + 1]
       ELSE
          /\ p2' = [p2 EXCEPT !.switchB = \lnot @]
    /\ p3' = p3 \cup {p}

Visit(p) ==
    IF p = Counter THEN CounterVisit ELSE NonCounterVisit(p)

Next ==
    \/ \E p \in Prisoner : Visit(p)
    \/ (p2.declared /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ \A p \in Prisoner : WF_vars(Visit(p))

\* Sums the values of a function f over its domain.
Sum(f) ==
    LET RECURSIVE SumAux(g, S) =
        IF S = {} THEN 0
        ELSE LET e = CHOOSE x \in S : TRUE IN
             g[e] + SumAux(g, S \setminus {e})
    IN SumAux(f, DOMAIN f)

CountInvariant ==
    LET totalTurnedUp = Sum(p2.turnedUp) IN
    totalTurnedUp = p2.count + (IF p2.switchA THEN 1 ELSE 0)

Safety == p2.declared => p3 = Prisoner

Liveness == <>p2.declared

=============================================================================