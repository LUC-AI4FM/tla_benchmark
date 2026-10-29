------------------------------- MODULE TLCMC -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS StateGraph,       \* [states |-> ..., initials |-> ..., actions |-> ...]
          ViolationStates,  \* states that violate the checked invariant
          null              \* model value distinct from all states

\* K = 1: strict BFS; K > 1: degraded (non-strict) BFS approximating K workers.
K == 1

ASSUME /\ K \in Nat \ {0}
       /\ StateGraph.initials \subseteq StateGraph.states
       /\ StateGraph.actions \subseteq (StateGraph.states \X StateGraph.states)
       /\ ViolationStates \subseteq StateGraph.states
       /\ null \notin StateGraph.states

Min(a, b) == IF a <= b THEN a ELSE b

Succ(s) == {t \in StateGraph.states : <<s, t>> \in StateGraph.actions}

-----------------------------------------------------------------------------
(* The set of known counterexamples: all finite paths through the graph   *)
(* starting in an initial state and ending in a violation state.           *)

N == Cardinality(StateGraph.states)

BSeq(S0, n) == UNION {[1..m -> S0] : m \in 1..n}

Paths ==
  {p \in BSeq(StateGraph.states, N) :
      /\ p[1] \in StateGraph.initials
      /\ \A j \in 1..(Len(p) - 1) : <<p[j], p[j+1]>> \in StateGraph.actions}

Counterexamples == {p \in Paths : p[Len(p)] \in ViolationStates}

Reachable == {p[Len(p)] : p \in Paths}

-----------------------------------------------------------------------------
(* Translated PlusCal algorithm                                            *)

VARIABLES S,               \* explored (seen) states
          C,               \* predecessor of each state (null if none)
          L,               \* BFS level of each state
          T,               \* queue of pending (unexplored) states
          i,               \* index into T of the state chosen by a worker
          state,           \* the state currently being expanded
          successors,      \* remaining successors of state to process
          counterexample,  \* the reconstructed counterexample trace
          pc

vars == <<S, C, L, T, i, state, successors, counterexample, pc>>

Init ==
  /\ S = {}
  /\ C = [s \in StateGraph.states |-> null]
  /\ L = [s \in StateGraph.states |-> 0]
  /\ T = <<>>
  /\ i = 1
  /\ state = null
  /\ successors = {}
  /\ counterexample = <<>>
  /\ pc = "init"

\* Check and enqueue the initial states one at a time.
init ==
  /\ pc = "init"
  /\ IF StateGraph.initials \subseteq S
       THEN /\ pc' = "loop"
            /\ UNCHANGED <<S, C, L, T, i, state, successors, counterexample>>
       ELSE \E s \in StateGraph.initials \ S :
              IF s \in ViolationStates
                THEN /\ counterexample' = <<s>>
                     /\ pc' = "trc"
                     /\ UNCHANGED <<S, C, L, T, i, state, successors>>
                ELSE /\ S' = S \cup {s}
                     /\ T' = Append(T, s)
                     /\ C' = [C EXCEPT ![s] = null]
                     /\ L' = [L EXCEPT ![s] = 0]
                     /\ pc' = "init"
                     /\ UNCHANGED <<i, state, successors, counterexample>>

\* Dequeue a state: strictly the head if K = 1, any of the first K otherwise.
loop ==
  /\ pc = "loop"
  /\ IF T = <<>>
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<S, C, L, T, i, state, successors, counterexample>>
       ELSE \E j \in 1..Min(K, Len(T)) :
              /\ i' = j
              /\ state' = T[j]
              /\ T' = SubSeq(T, 1, j - 1) \o SubSeq(T, j + 1, Len(T))
              /\ successors' = Succ(T[j]) \ S
              /\ pc' = "succs"
              /\ UNCHANGED <<S, C, L, counterexample>>

\* Process the successors of state one at a time.
succs ==
  /\ pc = "succs"
  /\ IF successors = {}
       THEN /\ pc' = "loop"
            /\ UNCHANGED <<S, C, L, T, i, state, successors, counterexample>>
       ELSE \E t \in successors :
              /\ successors' = successors \ {t}
              /\ IF t \in S
                   THEN /\ pc' = "succs"
                        /\ UNCHANGED <<S, C, L, T, counterexample>>
                   ELSE IF t \in ViolationStates
                     THEN /\ C' = [C EXCEPT ![t] = state]
                          /\ L' = [L EXCEPT ![t] = L[state] + 1]
                          /\ counterexample' = <<t>>
                          /\ pc' = "trc"
                          /\ UNCHANGED <<S, T>>
                     ELSE /\ S' = S \cup {t}
                          /\ T' = Append(T, t)
                          /\ C' = [C EXCEPT ![t] = state]
                          /\ L' = [L EXCEPT ![t] = L[state] + 1]
                          /\ pc' = "succs"
                          /\ UNCHANGED counterexample
              /\ UNCHANGED <<i, state>>

\* Reconstruct the counterexample by following predecessor links backwards.
trc ==
  /\ pc = "trc"
  /\ IF C[counterexample[1]] = null
       THEN /\ pc' = "Done"
            /\ UNCHANGED counterexample
       ELSE /\ counterexample' = <<C[counterexample[1]]>> \o counterexample
            /\ pc' = "trc"
  /\ UNCHANGED <<S, C, L, T, i, state, successors>>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == init \/ loop \/ succs \/ trc \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties                                                              *)

Termination == <>(pc = "Done")

ReachableViolations == ViolationStates \cap Reachable

Live ==
  ReachableViolations # {} =>
    <>[]( /\ pc = "Done"
          /\ counterexample \in Counterexamples
          /\ (K = 1 => \A p \in Counterexamples :
                          Len(counterexample) <= Len(p)) )

-----------------------------------------------------------------------------
(* Refinement mapping to the abstract reachability specification           *)
(* (MCReachability): the set of explored states only grows and always      *)
(* consists of reachable states; the abstract "found" flag corresponds to  *)
(* a nonempty counterexample.                                              *)

AbsExplored == S
AbsFound    == counterexample # <<>>

Refinement ==
  /\ [](AbsExplored \subseteq Reachable)
  /\ [][ /\ AbsExplored \subseteq AbsExplored'
         /\ (AbsFound => AbsFound') ]_<<S, counterexample>>
  /\ [](AbsFound /\ pc = "Done" =>
          counterexample[Len(counterexample)] \in ViolationStates)

=============================================================================