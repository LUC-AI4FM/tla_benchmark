---------------------------- MODULE Specification ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS M, N

ASSUME M \in Nat /\ M > 0
ASSUME N \in Nat /\ N > 0

Colors == {"Red", "Green", "Blue"}

VARIABLES
    agentState,      \* agentState[a] \in Colors \cup {"Faded"}
    agentMet,        \* agentMet[a] \in Nat - count of meetings for agent a
    rendezvous,      \* NONE or agent id waiting at rendezvous
    globalMet        \* global count of completed meetings

vars == <<agentState, agentMet, rendezvous, globalMet>>

Agents == 1..M

NONE == 0

\* Symmetric color transition function
\* When two agents meet, their new colors depend symmetrically on both colors
ColorTransition(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE 
        LET colors == {c1, c2} IN
        IF colors = {"Red", "Green"} THEN "Blue"
        ELSE IF colors = {"Red", "Blue"} THEN "Green"
        ELSE IF colors = {"Green", "Blue"} THEN "Red"
        ELSE c1  \* fallback, should not happen

TypeOK ==
    /\ agentState \in [Agents -> Colors \cup {"Faded"}]
    /\ agentMet \in [Agents -> Nat]
    /\ rendezvous \in {NONE} \cup Agents
    /\ globalMet \in Nat
    /\ globalMet <= N

SumMet == 
    LET Sum[S \in SUBSET Agents] ==
        IF S = {} THEN 0
        ELSE LET a == CHOOSE x \in S : TRUE
             IN agentMet[a] + Sum[S \ {a}]
    IN Sum[Agents]

Init ==
    /\ agentState \in [Agents -> Colors]
    /\ agentMet = [a \in Agents |-> 0]
    /\ rendezvous = NONE
    /\ globalMet = 0

\* Agent a attempts to enter the rendezvous when it's empty
EnterEmpty(a) ==
    /\ globalMet < N
    /\ agentState[a] \in Colors  \* agent is active
    /\ rendezvous = NONE
    /\ rendezvous' = a
    /\ UNCHANGED <<agentState, agentMet, globalMet>>

\* Agent a arrives and meets with waiting agent w
Meet(a, w) ==
    /\ globalMet < N
    /\ agentState[a] \in Colors  \* agent a is active
    /\ rendezvous = w
    /\ w # NONE
    /\ w # a
    /\ agentState[w] \in Colors  \* waiting agent is active
    /\ LET newColor == ColorTransition(agentState[a], agentState[w])
       IN agentState' = [agentState EXCEPT ![a] = newColor, ![w] = newColor]
    /\ agentMet' = [agentMet EXCEPT ![a] = agentMet[a] + 1, ![w] = agentMet[w] + 1]
    /\ globalMet' = globalMet + 1
    /\ rendezvous' = NONE

\* When budget reached, waiting agent becomes faded
FadeWaiting(a) ==
    /\ globalMet = N
    /\ rendezvous = a
    /\ agentState[a] \in Colors
    /\ agentState' = [agentState EXCEPT ![a] = "Faded"]
    /\ rendezvous' = NONE
    /\ UNCHANGED <<agentMet, globalMet>>

\* Active agent becomes faded when budget is reached and not waiting
FadeActive(a) ==
    /\ globalMet = N
    /\ rendezvous # a
    /\ agentState[a] \in Colors
    /\ agentState' = [agentState EXCEPT ![a] = "Faded"]
    /\ UNCHANGED <<agentMet, rendezvous, globalMet>>

Next ==
    \/ \E a \in Agents : EnterEmpty(a)
    \/ \E a \in Agents : \E w \in Agents : Meet(a, w)
    \/ \E a \in Agents : FadeWaiting(a)
    \/ \E a \in Agents : FadeActive(a)

Fairness ==
    /\ \A a \in Agents : WF_vars(EnterEmpty(a))
    /\ \A a \in Agents : \A w \in Agents : WF_vars(Meet(a, w))
    /\ \A a \in Agents : WF_vars(FadeWaiting(a))
    /\ \A a \in Agents : WF_vars(FadeActive(a))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: rendezvous holds at most one agent
RendezvousAtMostOne ==
    rendezvous \in {NONE} \cup Agents

\* Safety: global counter only increases properly (captured by TypeOK and transition rules)
GlobalCounterMonotonic ==
    globalMet <= N

\* Termination property: once globalMet = N, all agents eventually become Faded
AllFaded ==
    \A a \in Agents : agentState[a] = "Faded"

Termination ==
    (globalMet = N) ~> AllFaded

\* Accounting invariant: when globalMet = N, sum of all meeting counts = 2*N
AccountingInvariant ==
    (globalMet = N /\ rendezvous = NONE) => (SumMet = 2 * N)

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ RendezvousAtMostOne
    /\ GlobalCounterMonotonic
    /\ (globalMet < N) => (SumMet = 2 * globalMet)
    /\ (rendezvous # NONE) => (SumMet = 2 * globalMet)

=============================================================================