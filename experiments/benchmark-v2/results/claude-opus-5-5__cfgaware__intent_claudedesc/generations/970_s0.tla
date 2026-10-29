------------------------------- MODULE ModelChecker -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    StateGraph,       \* [states |-> ..., initials |-> ..., actions |-> {<<s,t>>, ...}]
    ViolationStates,  \* Set of states that violate the safety property
    null              \* A model value distinct from all states

\* Worker count K: window size for non-strict BFS (K = 1 means strict BFS).
K == 1

\* State constraint predicate, evaluated on a state at its BFS level.
Constraint(s, lvl) == TRUE

ASSUME StateGraph.initials \subseteq StateGraph.states
ASSUME \A a \in StateGraph.actions : a[1] \in StateGraph.states /\ a[2] \in StateGraph.states
ASSUME null \notin StateGraph.states
ASSUME K \in Nat \ {0}

-----------------------------------------------------------------------------------
\* Helpers

SuccessorsOf(s) == { t \in StateGraph.states : <<s, t>> \in StateGraph.actions }

SetToSeq(X) ==
    CHOOSE f \in [1..Cardinality(X) -> X] :
        \A a, b \in DOMAIN f : a # b => f[a] # f[b]

RemoveAt(seq, j) == SubSeq(seq, 1, j - 1) \o SubSeq(seq, j + 1, Len(seq))

Min(a, b) == IF a < b THEN a ELSE b

ReachableStates ==
    LET R[n \in Nat] ==
            IF n = 0 THEN StateGraph.initials
            ELSE R[n - 1] \cup UNION { SuccessorsOf(s) : s \in R[n - 1] }
    IN R[Cardinality(StateGraph.states)]

\* States without outgoing transitions other than self-loops.
DeadlockStates == { s \in StateGraph.states : SuccessorsOf(s) \ {s} = {} }

IsPath(p) ==
    /\ Len(p) > 0
    /\ p[1] \in StateGraph.initials
    /\ \A j \in 1..(Len(p) - 1) : <<p[j], p[j + 1]>> \in StateGraph.actions

AllPaths ==
    { p \in UNION { [1..n -> StateGraph.states] : n \in 1..Cardinality(StateGraph.states) } :
        IsPath(p) }

\* The set of known valid counterexamples.
ViolationCounterexamples == { p \in AllPaths : p[Len(p)] \in ViolationStates }
DeadlockCounterexamples  == { p \in AllPaths : p[Len(p)] \in DeadlockStates }
Counterexamples == ViolationCounterexamples \cup DeadlockCounterexamples

-----------------------------------------------------------------------------------
VARIABLES
    S,               \* Set of seen (visited) states
    C,               \* The BFS queue (frontier)
    T,               \* Predecessor relation: set of <<pred, succ>>
    L,               \* BFS level of each state (-1 if not yet seen)
    counterexample,  \* The counterexample trace
    state,           \* The state currently being explored
    successors,      \* Successors of state yet to be processed
    i,               \* Trace reconstruction counter
    pc

vars == <<S, C, T, L, counterexample, state, successors, i, pc>>

Init ==
    /\ S = {}
    /\ C = <<>>
    /\ T = {}
    /\ L = [s \in StateGraph.states |-> -1]
    /\ counterexample = <<>>
    /\ state = null
    /\ successors = {}
    /\ i = 0
    /\ pc = "init"

\* Check all initial states before exploring any successors.
init ==
    /\ pc = "init"
    /\ S' = StateGraph.initials
    /\ L' = [s \in StateGraph.states |-> IF s \in StateGraph.initials THEN 0 ELSE -1]
    /\ IF StateGraph.initials \cap ViolationStates # {}
         THEN /\ state' = CHOOSE s \in StateGraph.initials \cap ViolationStates : TRUE
              /\ C' = <<>>
              /\ pc' = "trc"
         ELSE /\ C' = SetToSeq({ s \in StateGraph.initials : Constraint(s, 0) })
              /\ state' = null
              /\ pc' = "loop"
    /\ UNCHANGED <<T, counterexample, successors, i>>

\* Dequeue a state from the window of the first K queue elements.
loop ==
    /\ pc = "loop"
    /\ IF C # <<>>
         THEN \E j \in 1..Min(K, Len(C)) :
                /\ state' = C[j]
                /\ C' = RemoveAt(C, j)
                /\ state' \in S
                /\ successors' = SuccessorsOf(C[j]) \ {C[j]}
                /\ IF successors' = {}
                     THEN pc' = "trc"      \* deadlock
                     ELSE pc' = "each"
         ELSE /\ pc' = "Done"
              /\ UNCHANGED <<C, state, successors>>
    /\ UNCHANGED <<S, T, L, counterexample, i>>

\* Process the successors of the current state one by one.
each ==
    /\ pc = "each"
    /\ IF successors # {}
         THEN \E t \in successors :
                /\ successors' = successors \ {t}
                /\ IF t \notin S
                     THEN /\ S' = S \cup {t}
                          /\ T' = T \cup {<<state, t>>}
                          /\ L' = [L EXCEPT ![t] = L[state] + 1]
                          /\ IF t \in ViolationStates
                               THEN /\ state' = t
                                    /\ pc' = "trc"
                                    /\ C' = C
                               ELSE /\ state' = state
                                    /\ pc' = "each"
                                    /\ IF Constraint(t, L[state] + 1)
                                         THEN C' = Append(C, t)
                                         ELSE C' = C
                     ELSE /\ UNCHANGED <<S, T, L, C, state>>
                          /\ pc' = "each"
         ELSE /\ pc' = "loop"
              /\ UNCHANGED <<S, T, L, C, state, successors>>
    /\ UNCHANGED <<counterexample, i>>

\* Reconstruct the counterexample by following the predecessor relation.
trc ==
    /\ pc = "trc"
    /\ counterexample' = <<state>> \o counterexample
    /\ i' = i + 1
    /\ IF \E p \in StateGraph.states : <<p, state>> \in T
         THEN /\ state' = CHOOSE p \in StateGraph.states : <<p, state>> \in T
              /\ pc' = "trc"
         ELSE /\ state' = state
              /\ pc' = "Done"
    /\ UNCHANGED <<S, C, T, L, successors>>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == init \/ loop \/ each \/ trc \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------------
\* Properties

TypeOK ==
    /\ S \subseteq StateGraph.states
    /\ T \subseteq StateGraph.actions
    /\ pc \in {"init", "loop", "each", "trc", "Done"}
    /\ i \in Nat

\* If exploration completes without a violation, the queue is empty.
EmptyQueueOnSuccess ==
    (pc = "Done" /\ counterexample = <<>>) => C = <<>>

\* Every explored state has been marked visited.
ExploredSeen ==
    pc = "each" => state \in S

Termination == <>(pc = "Done")

ViolationReachable ==
    ReachableStates \cap (ViolationStates \cup DeadlockStates) # {}

Live ==
    ViolationReachable => <>(pc = "Done" /\ counterexample \in Counterexamples)

ValidCounterexample ==
    (pc = "Done" /\ counterexample # <<>>) =>
        /\ counterexample \in Counterexamples
        /\ (K = 1 /\ counterexample[Len(counterexample)] \in ViolationStates) =>
              \A p \in ViolationCounterexamples : Len(counterexample) <= Len(p)

Refinement ==
    /\ [](TypeOK /\ EmptyQueueOnSuccess /\ ExploredSeen /\ ValidCounterexample)
    /\ [][pc = "Done" => UNCHANGED vars]_vars

===================================================================================