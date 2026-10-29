---------------------------- MODULE ChameneosRendezvous ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    M,              \* number of agents (positive integer)
    N,              \* global meeting budget (positive integer)
    Colors,         \* the fixed set of three initial colors
    Faded,          \* distinguished value denoting an inactive agent
    Complement(_, _) \* abstract deterministic, symmetric color-transition function

ASSUME MPositive     == M \in Nat \ {0}
ASSUME NPositive     == N \in Nat \ {0}
ASSUME ThreeColors   == Cardinality(Colors) = 3
ASSUME FadedDistinct == Faded \notin Colors
ASSUME ComplementType ==
    \A c1, c2 \in Colors : Complement(c1, c2) \in Colors
ASSUME ComplementSymmetric ==
    \A c1, c2 \in Colors : Complement(c1, c2) = Complement(c2, c1)

Agents == 1..M
NoAgent == 0          \* value of the rendezvous when it is empty

VARIABLES
    color,      \* color[a] \in Colors \cup {Faded}
    meetings,   \* meetings[a] : number of meetings recorded by agent a
    place,      \* the rendezvous: NoAgent (empty) or the single waiting agent
    count       \* global counter of completed meetings

vars == <<color, meetings, place, count>>

-----------------------------------------------------------------------------
\* Helpers

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN  f[x] + SumOver(f, S \ {x})

TotalMeetings == SumOver(meetings, Agents)

Active(a) == color[a] # Faded

Waiting == { a \in Agents : place = a }

-----------------------------------------------------------------------------
TypeOK ==
    /\ color \in [Agents -> Colors \cup {Faded}]
    /\ meetings \in [Agents -> Nat]
    /\ place \in Agents \cup {NoAgent}
    /\ count \in 0..N

Init ==
    /\ color \in [Agents -> Colors]
    /\ meetings = [a \in Agents |-> 0]
    /\ place = NoAgent
    /\ count = 0

\* Agent a arrives at the empty rendezvous and waits there.
Enter(a) ==
    /\ count < N
    /\ Active(a)
    /\ place = NoAgent
    /\ place' = a
    /\ UNCHANGED <<color, meetings, count>>

\* Agent a arrives while agent b = place is waiting: the two meet.
Meet(a) ==
    /\ count < N
    /\ Active(a)
    /\ place # NoAgent
    /\ place # a
    /\ LET b == place
           nc == Complement(color[a], color[b])
       IN  /\ color' = [color EXCEPT ![a] = nc, ![b] = nc]
           /\ meetings' = [meetings EXCEPT ![a] = @ + 1, ![b] = @ + 1]
    /\ count' = count + 1
    /\ place' = NoAgent

\* Once the budget is exhausted, an active agent fades permanently
\* (a waiting agent leaves the rendezvous as it fades).
Fade(a) ==
    /\ count >= N
    /\ Active(a)
    /\ color' = [color EXCEPT ![a] = Faded]
    /\ place' = IF place = a THEN NoAgent ELSE place
    /\ UNCHANGED <<meetings, count>>

\* All agents faded: the system terminates (stuttering allowed).
Terminated ==
    /\ \A a \in Agents : color[a] = Faded
    /\ UNCHANGED vars

Progress == \E a \in Agents : Enter(a) \/ Meet(a)

Next ==
    \/ \E a \in Agents : Enter(a) \/ Meet(a) \/ Fade(a)
    \/ Terminated

Fairness ==
    /\ WF_vars(Progress)
    /\ \A a \in Agents : WF_vars(Fade(a))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* SAFETY INVARIANTS

\* The rendezvous never holds more than one waiting agent,
\* and a waiting agent is always active.
AtMostOneWaiting ==
    /\ Cardinality(Waiting) <= 1
    /\ place # NoAgent => Active(place)

\* Counter never exceeds the budget.
CounterBounded == count <= N

\* Each completed pair adds exactly two to the sum of recorded meetings.
SumInvariant == TotalMeetings = 2 * count

\* Accounting invariant as stated.
AccountingInvariant == (count = N) => (TotalMeetings = 2 * N)

\* Once the budget is reached, every agent is inactive or cannot
\* increase the counter.
TerminationConsistency ==
    (count = N) =>
        \A a \in Agents :
            \/ color[a] = Faded
            \/ (~ENABLED Meet(a) /\ ~ENABLED Enter(a))

\* Faded agents are never waiting (inactivity implies no participation).
FadedOnlyAfterBudget ==
    (\E a \in Agents : color[a] = Faded) => count = N

Invariants ==
    /\ TypeOK
    /\ AtMostOneWaiting
    /\ CounterBounded
    /\ SumInvariant
    /\ AccountingInvariant
    /\ TerminationConsistency
    /\ FadedOnlyAfterBudget

-----------------------------------------------------------------------------
\* SAFETY (ACTION) PROPERTIES

\* The counter only changes by +1, and only when exactly two distinct agents
\* finish a meeting: both record one more meeting, both get the symmetric
\* new color, and every other agent is untouched.
CounterOnlyOnMeeting ==
    [][ count' # count =>
          /\ count' = count + 1
          /\ \E a, b \in Agents :
               /\ a # b
               /\ color'[a] = Complement(color[a], color[b])
               /\ color'[b] = Complement(color[b], color[a])
               /\ color'[a] = color'[b]
               /\ meetings'[a] = meetings[a] + 1
               /\ meetings'[b] = meetings[b] + 1
               /\ \A c \in Agents \ {a, b} :
                    /\ color'[c] = color[c]
                    /\ meetings'[c] = meetings[c]
      ]_vars

\* Meeting counts of agents change only together with the global counter.
MeetingsChangeOnlyWithCounter ==
    [][ meetings' # meetings => count' = count + 1 ]_vars

\* The counter is monotonic.
CounterMonotonic == [][ count' >= count ]_vars

\* Once the budget is reached, the counter is frozen.
BudgetFrozen == [][ count = N => count' = N ]_vars

\* Faded is permanent.
FadedPermanent ==
    \A a \in Agents : [][ color[a] = Faded => color'[a] = Faded ]_vars

-----------------------------------------------------------------------------
\* LIVENESS PROPERTIES

\* With at least two agents, the meeting budget is eventually exhausted.
EventuallyBudgetReached == (M >= 2) => <>(count = N)

\* Once the budget is reached, all agents eventually fade.
EventuallyAllFaded ==
    (count = N) ~> (\A a \in Agents : color[a] = Faded)

\* Overall termination (for M >= 2).
EventuallyTerminates ==
    (M >= 2) => <>[](\A a \in Agents : color[a] = Faded)

=============================================================================