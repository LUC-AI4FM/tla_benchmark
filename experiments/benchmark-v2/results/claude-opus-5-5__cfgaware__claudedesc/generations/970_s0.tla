------------------------------- MODULE TLCMC -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS StateGraph,      \* [states |-> ..., initials |-> ..., actions |-> [s \in states |-> SUBSET states]]
          ViolationStates, \* set of error states
          null             \* model value distinct from all states

ASSUME /\ StateGraph.initials \subseteq StateGraph.states
       /\ \A s \in StateGraph.states : StateGraph.actions[s] \subseteq StateGraph.states
       /\ ViolationStates \subseteq StateGraph.states
       /\ null \notin StateGraph.states

(***************************************************************************)
(* BFS window size: K = 1 is strict BFS, K > 1 models TLC's degraded BFS   *)
(* with multiple workers (any of the first K queued states may be taken).  *)
(***************************************************************************)
K == 1
ASSUME K \in (Nat \ {0})

(* State constraint: may prune state s at BFS level l. *)
Constraint(s, l) == TRUE

(* Deadlock checking is disabled (deadlocked states are not errors). *)
CheckDeadlock == FALSE

Min(a, b) == IF a < b THEN a ELSE b

Range(f) == {f[x] : x \in DOMAIN f}

(* All simple paths from an initial state to a violation state. *)
Counterexamples ==
    { p \in UNION { [1..n -> StateGraph.states] :
                       n \in 1..Cardinality(StateGraph.states) } :
        /\ p[1] \in StateGraph.initials
        /\ p[Len(p)] \in ViolationStates
        /\ \A j, k \in 1..Len(p) : j # k => p[j] # p[k]
        /\ \A j \in 1..(Len(p) - 1) : p[j+1] \in StateGraph.actions[p[j]] }

MinLength ==
    CHOOSE n \in {Len(p) : p \in Counterexamples} :
        \A q \in Counterexamples : n <= Len(q)

ConstrainedInits == {s \in StateGraph.initials : Constraint(s, 0)}

Permutations(X) ==
    { f \in [1..Cardinality(X) -> X] : \A x \in X : \E j \in 1..Cardinality(X) : f[j] = x }

RemoveAt(seq, j) == SubSeq(seq, 1, j - 1) \o SubSeq(seq, j + 1, Len(seq))

VARIABLES S, C, state, successors, i, counterexample, T, L, pc

vars == <<S, C, state, successors, i, counterexample, T, L, pc>>

Init ==
    /\ S \in Permutations(ConstrainedInits)
    /\ C = {}
    /\ state = null
    /\ successors = {}
    /\ i = 1
    /\ counterexample = <<>>
    /\ T = {}
    /\ L = [s \in StateGraph.states |-> 0]
    /\ pc = "init_chk"

(* Check initial states for violations and mark them explored. *)
InitCheck ==
    /\ pc = "init_chk"
    /\ IF i <= Len(S)
         THEN IF S[i] \in ViolationStates
                THEN /\ counterexample' = <<S[i]>>
                     /\ pc' = "Done"
                     /\ UNCHANGED <<S, C, state, successors, i, T, L>>
                ELSE /\ C' = C \cup {S[i]}
                     /\ i' = i + 1
                     /\ pc' = "init_chk"
                     /\ UNCHANGED <<S, state, successors, counterexample, T, L>>
         ELSE /\ pc' = "w1"
              /\ UNCHANGED <<S, C, state, successors, i, counterexample, T, L>>

(* Dequeue one of the first K states of the queue. *)
Dequeue ==
    /\ pc = "w1"
    /\ IF S # <<>>
         THEN \E j \in 1..Min(K, Len(S)) :
                /\ state' = S[j]
                /\ S' = RemoveAt(S, j)
                /\ successors' = { t \in StateGraph.actions[S[j]] :
                                     /\ t \notin C
                                     /\ Constraint(t, L[S[j]] + 1) }
                /\ IF CheckDeadlock /\ StateGraph.actions[S[j]] = {}
                     THEN /\ counterexample' = <<S[j]>>
                          /\ pc' = "trc"
                     ELSE /\ pc' = "w2"
                          /\ UNCHANGED counterexample
                /\ UNCHANGED <<C, i, T, L>>
         ELSE /\ pc' = "Done"
              /\ UNCHANGED <<S, C, state, successors, i, counterexample, T, L>>

(* Explore the successors of the current state. *)
Explore ==
    /\ pc = "w2"
    /\ IF successors # {}
         THEN \E succ \in successors :
                /\ successors' = successors \ {succ}
                /\ C' = C \cup {succ}
                /\ T' = T \cup {<<state, succ>>}
                /\ L' = [L EXCEPT ![succ] = L[state] + 1]
                /\ S' = Append(S, succ)
                /\ IF succ \in ViolationStates
                     THEN /\ counterexample' = <<succ>>
                          /\ pc' = "trc"
                     ELSE /\ pc' = "w2"
                          /\ UNCHANGED counterexample
                /\ UNCHANGED <<state, i>>
         ELSE /\ pc' = "w1"
              /\ UNCHANGED <<S, C, state, successors, i, counterexample, T, L>>

(* Reconstruct the counterexample back to an initial state. *)
Trace ==
    /\ pc = "trc"
    /\ IF \E p \in StateGraph.states : <<p, Head(counterexample)>> \in T
         THEN /\ \E p \in StateGraph.states :
                   /\ <<p, Head(counterexample)>> \in T
                   /\ counterexample' = <<p>> \o counterexample
              /\ pc' = "trc"
         ELSE /\ pc' = "Done"
              /\ UNCHANGED counterexample
    /\ UNCHANGED <<S, C, state, successors, i, T, L>>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == InitCheck \/ Dequeue \/ Explore \/ Trace \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(InitCheck)
        /\ WF_vars(Dequeue)
        /\ WF_vars(Explore)
        /\ WF_vars(Trace)

-----------------------------------------------------------------------------

Termination == <>(pc = "Done")

Live ==
    (Counterexamples # {}) =>
        <>( /\ pc = "Done"
            /\ counterexample \in Counterexamples
            /\ (K = 1 => Len(counterexample) = MinLength) )

-----------------------------------------------------------------------------
(* Refinement mapping to the set-based nondeterministic exploration        *)
(* (MCReachability): the set of discovered states is C \cup Range(S).      *)
-----------------------------------------------------------------------------

visitedBar == C \cup Range(S)

RInit == visitedBar = ConstrainedInits

RNext ==
    \E s \in visitedBar :
      \E t \in StateGraph.actions[s] :
         /\ t \notin visitedBar
         /\ visitedBar' = visitedBar \cup {t}

Refinement == RInit /\ [][RNext]_visitedBar

=============================================================================