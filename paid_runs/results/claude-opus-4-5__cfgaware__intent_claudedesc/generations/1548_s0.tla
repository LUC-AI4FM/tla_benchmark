---------------------------- MODULE OneStepByzantine ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat
       /\ F \in Nat
       /\ F <= T
       /\ N > 3 * T

VARIABLES
    pcState,           \* Function from process id to state: "init", "proposed", "decided"
    proposal,          \* Function from process id to initial proposal: 0 or 1
    decision,          \* Function from process id to decision: -1 (none), 0, 1, or 2 (undecided)
    correctMsgs0,      \* Count of "0" messages from correct processes
    correctMsgs1,      \* Count of "1" messages from correct processes
    faultyMsgs0,       \* Count of "0" messages from faulty processes
    faultyMsgs1,       \* Count of "1" messages from faulty processes
    numFaulty,         \* Current number of activated Byzantine processes
    correctProposed,   \* Set of correct processes that have proposed
    faultyActivated    \* Set of faulty processes that have been activated

vars == <<pcState, proposal, decision, correctMsgs0, correctMsgs1, 
          faultyMsgs0, faultyMsgs1, numFaulty, correctProposed, faultyActivated>>

Procs == 1..N

\* All correct processes start with proposal 0
InitAllZeros ==
    /\ pcState = [p \in Procs |-> "init"]
    /\ proposal = [p \in Procs |-> 0]
    /\ decision = [p \in Procs |-> -1]
    /\ correctMsgs0 = 0
    /\ correctMsgs1 = 0
    /\ faultyMsgs0 = 0
    /\ faultyMsgs1 = 0
    /\ numFaulty = 0
    /\ correctProposed = {}
    /\ faultyActivated = {}

\* All correct processes start with proposal 1
InitAllOnes ==
    /\ pcState = [p \in Procs |-> "init"]
    /\ proposal = [p \in Procs |-> 1]
    /\ decision = [p \in Procs |-> -1]
    /\ correctMsgs0 = 0
    /\ correctMsgs1 = 0
    /\ faultyMsgs0 = 0
    /\ faultyMsgs1 = 0
    /\ numFaulty = 0
    /\ correctProposed = {}
    /\ faultyActivated = {}

\* General initialization with arbitrary proposals
Init ==
    /\ pcState = [p \in Procs |-> "init"]
    /\ proposal \in [Procs -> {0, 1}]
    /\ decision = [p \in Procs |-> -1]
    /\ correctMsgs0 = 0
    /\ correctMsgs1 = 0
    /\ faultyMsgs0 = 0
    /\ faultyMsgs1 = 0
    /\ numFaulty = 0
    /\ correctProposed = {}
    /\ faultyActivated = {}

\* A correct process proposes its value (broadcasts message)
Propose(p) ==
    /\ p \notin faultyActivated
    /\ pcState[p] = "init"
    /\ pcState' = [pcState EXCEPT ![p] = "proposed"]
    /\ IF proposal[p] = 0
       THEN /\ correctMsgs0' = correctMsgs0 + 1
            /\ correctMsgs1' = correctMsgs1
       ELSE /\ correctMsgs1' = correctMsgs1 + 1
            /\ correctMsgs0' = correctMsgs0
    /\ correctProposed' = correctProposed \cup {p}
    /\ UNCHANGED <<proposal, decision, faultyMsgs0, faultyMsgs1, numFaulty, faultyActivated>>

\* Total messages received
TotalMsgs0 == correctMsgs0 + faultyMsgs0
TotalMsgs1 == correctMsgs1 + faultyMsgs1
TotalMsgs == TotalMsgs0 + TotalMsgs1

\* Number of correct processes
NumCorrect == N - numFaulty

\* A correct process decides based on received messages
Decide(p) ==
    /\ p \notin faultyActivated
    /\ pcState[p] = "proposed"
    /\ TotalMsgs >= N - T  \* Received at least N-T messages
    /\ pcState' = [pcState EXCEPT ![p] = "decided"]
    /\ decision' = [decision EXCEPT ![p] = 
        IF TotalMsgs0 >= N - T THEN 0
        ELSE IF TotalMsgs1 >= N - T THEN 1
        ELSE IF proposal[p] = 0 THEN 0
        ELSE IF proposal[p] = 1 THEN 1
        ELSE 2]  \* Undecided fallback (should use own proposal)
    /\ UNCHANGED <<proposal, correctMsgs0, correctMsgs1, faultyMsgs0, faultyMsgs1, 
                   numFaulty, correctProposed, faultyActivated>>

\* Activate a Byzantine process (can happen to any process not yet faulty, up to F)
ActivateFaulty(p) ==
    /\ numFaulty < F
    /\ p \notin faultyActivated
    /\ pcState[p] = "init"  \* Can only become faulty before proposing
    /\ numFaulty' = numFaulty + 1
    /\ faultyActivated' = faultyActivated \cup {p}
    /\ UNCHANGED <<pcState, proposal, decision, correctMsgs0, correctMsgs1, 
                   faultyMsgs0, faultyMsgs1, correctProposed>>

\* Byzantine process sends arbitrary message (0 or 1)
FaultySend(p, v) ==
    /\ p \in faultyActivated
    /\ IF v = 0
       THEN /\ faultyMsgs0' = faultyMsgs0 + 1
            /\ faultyMsgs1' = faultyMsgs1
       ELSE /\ faultyMsgs1' = faultyMsgs1 + 1
            /\ faultyMsgs0' = faultyMsgs0
    /\ UNCHANGED <<pcState, proposal, decision, correctMsgs0, correctMsgs1, 
                   numFaulty, correctProposed, faultyActivated>>

\* Combined next-state relation
Next ==
    \/ \E p \in Procs : Propose(p)
    \/ \E p \in Procs : Decide(p)
    \/ \E p \in Procs : ActivateFaulty(p)
    \/ \E p \in Procs, v \in {0, 1} : FaultySend(p, v)

\* Fairness: correct processes eventually propose and decide
Fairness ==
    /\ \A p \in Procs : WF_vars(Propose(p))
    /\ \A p \in Procs : WF_vars(Decide(p))

\* Main specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Type invariant
TypeOK ==
    /\ pcState \in [Procs -> {"init", "proposed", "decided"}]
    /\ proposal \in [Procs -> {0, 1}]
    /\ decision \in [Procs -> {-1, 0, 1, 2}]
    /\ correctMsgs0 \in 0..N
    /\ correctMsgs1 \in 0..N
    /\ faultyMsgs0 \in 0..N
    /\ faultyMsgs1 \in 0..N
    /\ numFaulty \in 0..F
    /\ correctProposed \subseteq Procs
    /\ faultyActivated \subseteq Procs

\* Helper: all correct processes proposed 0 initially
AllCorrectProposed0 ==
    \A p \in Procs : p \notin faultyActivated => proposal[p] = 0

\* Helper: all correct processes proposed 1 initially
AllCorrectProposed1 ==
    \A p \in Procs : p \notin faultyActivated => proposal[p] = 1

\* Helper: correct processes
CorrectProcs == Procs \ faultyActivated

\* Property 1: If all correct processes initially propose 0, 
\* no correct process ever decides 1 or enters undecided state
NoDecide1OrUndecided ==
    \A p \in Procs : 
        (p \notin faultyActivated /\ pcState[p] = "decided") => 
        (decision[p] # 1 /\ decision[p] # 2)

OneStep0_Ltl ==
    (\A p \in Procs : proposal[p] = 0) => []NoDecide1OrUndecided

\* Property 2: If all correct processes initially propose 1,
\* they all eventually decide 1 and never enter undecided state
AllCorrectDecide1 ==
    \A p \in Procs :
        (p \notin faultyActivated /\ pcState[p] = "decided") =>
        (decision[p] = 1 /\ decision[p] # 2)

EventuallyAllCorrectDecide1 ==
    \A p \in Procs :
        (p \notin faultyActivated) => <>(pcState[p] = "decided" /\ decision[p] = 1)

OneStep1_Ltl ==
    (\A p \in Procs : proposal[p] = 1) => 
    ([]AllCorrectDecide1 /\ EventuallyAllCorrectDecide1)

\* Property 3: Under all-ones initialization, every process eventually decides 1
AllDecideOne ==
    (\A p \in Procs : proposal[p] = 1) =>
    <>(\A p \in Procs : (p \notin faultyActivated => (pcState[p] = "decided" /\ decision[p] = 1)))

=============================================================================