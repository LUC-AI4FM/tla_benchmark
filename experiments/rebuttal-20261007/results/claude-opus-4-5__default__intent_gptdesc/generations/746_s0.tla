---------------------------- MODULE Rendezvous ----------------------------
EXTENDS Integers, FiniteSets, Naturals

CONSTANTS M, N, Colors, TransitionFunc

ASSUME M \in Nat /\ M > 0
ASSUME N \in Nat /\ N > 0
ASSUME Colors # {}
ASSUME TransitionFunc \in [Colors \X Colors -> Colors]
\* Symmetric: TransitionFunc[c1, c2] = TransitionFunc[c2, c1] for all c1, c2 in Colors

VARIABLES
    agentState,      \* Function from agents to their current color state
    agentMeetings,   \* Function from agents to count of meetings participated in
    agentActive,     \* Function from agents to BOOLEAN (TRUE = active, FALSE = faded/inactive)
    rendezvous,      \* Either {} (empty) or a singleton set containing the waiting agent
    globalCounter    \* Count of completed pair meetings

Agents == 1..M

vars == <<agentState, agentMeetings, agentActive, rendezvous, globalCounter>>

TypeOK ==
    /\ agentState \in [Agents -> Colors]
    /\ agentMeetings \in [Agents -> Nat]
    /\ agentActive \in [Agents -> BOOLEAN]
    /\ rendezvous \subseteq Agents
    /\ Cardinality(rendezvous) <= 1
    /\ globalCounter \in 0..N

\* Pick an arbitrary initial color for each agent from the set of Colors
Init ==
    /\ agentState \in [Agents -> Colors]
    /\ agentMeetings = [a \in Agents |-> 0]
    /\ agentActive = [a \in Agents |-> TRUE]
    /\ rendezvous = {}
    /\ globalCounter = 0

\* Agent a attempts to enter an empty rendezvous and waits
EnterAndWait(a) ==
    /\ agentActive[a] = TRUE
    /\ rendezvous = {}
    /\ globalCounter < N
    /\ rendezvous' = {a}
    /\ UNCHANGED <<agentState, agentMeetings, agentActive, globalCounter>>

\* Agent a arrives and meets with waiting agent w
Meet(a, w) ==
    /\ agentActive[a] = TRUE
    /\ agentActive[w] = TRUE
    /\ rendezvous = {w}
    /\ a # w
    /\ globalCounter < N
    /\ LET oldStateA == agentState[a]
           oldStateW == agentState[w]
           newState == TransitionFunc[oldStateA, oldStateW]
       IN
           /\ agentState' = [agentState EXCEPT ![a] = newState, ![w] = newState]
           /\ agentMeetings' = [agentMeetings EXCEPT ![a] = @ + 1, ![w] = @ + 1]
           /\ globalCounter' = globalCounter + 1
           /\ rendezvous' = {}
           /\ UNCHANGED agentActive

\* When budget is exhausted, waiting agent becomes inactive (faded)
FadeWaitingAgent(w) ==
    /\ globalCounter = N
    /\ rendezvous = {w}
    /\ agentActive[w] = TRUE
    /\ agentActive' = [agentActive EXCEPT ![w] = FALSE]
    /\ rendezvous' = {}
    /\ UNCHANGED <<agentState, agentMeetings, globalCounter>>

\* Active agent that would try to enter but budget exhausted becomes inactive
FadeActiveAgent(a) ==
    /\ globalCounter = N
    /\ agentActive[a] = TRUE
    /\ a \notin rendezvous
    /\ agentActive' = [agentActive EXCEPT ![a] = FALSE]
    /\ UNCHANGED <<agentState, agentMeetings, rendezvous, globalCounter>>

Next ==
    \/ \E a \in Agents : EnterAndWait(a)
    \/ \E a, w \in Agents : Meet(a, w)
    \/ \E w \in Agents : FadeWaitingAgent(w)
    \/ \E a \in Agents : FadeActiveAgent(a)

\* Fairness: every agent eventually gets a chance to act
Fairness ==
    /\ \A a \in Agents : WF_vars(EnterAndWait(a))
    /\ \A a, w \in Agents : WF_vars(Meet(a, w))
    /\ \A w \in Agents : WF_vars(FadeWaitingAgent(w))
    /\ \A a \in Agents : WF_vars(FadeActiveAgent(a))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* SAFETY INVARIANTS

\* The rendezvous holds at most one waiting agent
RendezvousAtMostOne ==
    Cardinality(rendezvous) <= 1

\* Global counter only increases (never decreases) - captured by TypeOK and Next definition
GlobalCounterBounded ==
    globalCounter <= N

\* Sum of all agent meeting counts
TotalAgentMeetings ==
    LET Sum[S \in SUBSET Agents] ==
        IF S = {} THEN 0
        ELSE LET a == CHOOSE x \in S : TRUE
             IN agentMeetings[a] + Sum[S \ {a}]
    IN Sum[Agents]

\* Accounting invariant: total meetings = 2 * globalCounter (each pair adds 2)
AccountingInvariant ==
    TotalAgentMeetings = 2 * globalCounter

\* When counter reaches N, accounting is exact
AccountingAtN ==
    (globalCounter = N) => (TotalAgentMeetings = 2 * N)

\* Only active agents can be in rendezvous
RendezvousOnlyActive ==
    \A a \in rendezvous : agentActive[a] = TRUE

\* Combined safety invariant
Safety ==
    /\ TypeOK
    /\ RendezvousAtMostOne
    /\ GlobalCounterBounded
    /\ AccountingInvariant
    /\ RendezvousOnlyActive

-----------------------------------------------------------------------------
\* TERMINATION AND CONSISTENCY PROPERTIES

\* Once counter reaches N, no agent can increase it further
NoFurtherMeetingsAfterN ==
    (globalCounter = N) => [][globalCounter' = N]_globalCounter

\* All agents eventually become inactive or counter is at N
AllAgentsEventuallyInactiveOrDone ==
    <>(globalCounter = N /\ \A a \in Agents : agentActive[a] = FALSE)

\* The system eventually reaches the budget
EventuallyReachBudget ==
    <>(globalCounter = N)

\* Once at N with empty rendezvous, all agents eventually fade
TerminationConsistency ==
    [](globalCounter = N => <>(\A a \in Agents : agentActive[a] = FALSE))

\* Liveness: the system makes progress until termination
Progress ==
    (globalCounter < N /\ \E a \in Agents : agentActive[a]) ~> (globalCounter > globalCounter \/ globalCounter = N)

=============================================================================