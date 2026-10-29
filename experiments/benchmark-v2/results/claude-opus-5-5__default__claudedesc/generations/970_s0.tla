------------------------------ MODULE TLCMC ---------------------------------
(***************************************************************************)
(* A breadth-first-search model checker in the style of TLC.  It explores *)
(* a directed state graph, looks for violation (error) states, and builds *)
(* a counterexample trace back to an initial state from the recorded      *)
(* predecessor pairs.                                                     *)
(*                                                                         *)
(* K = 1 models strict BFS.  K > 1 models TLC's degraded BFS with several *)
(* workers: any of the first K queued states may be dequeued.             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    StateGraph,        \* [states |-> ..., initials |-> ..., actions |-> ...]
                       \* actions is a set of pairs <<s, t>>
    ViolationStates,   \* the error states
    K,                 \* BFS window size
    Constraint(_, _),  \* Constraint(s, level) prunes state s at a BFS level
    Counterexamples    \* the set of known counterexample sequences

ASSUME /\ K \in Nat \ {0}
       /\ StateGraph.initials \subseteq StateGraph.states
       /\ StateGraph.actions \subseteq (StateGraph.states \X StateGraph.states)
       /\ ViolationStates \subseteq StateGraph.states

VARIABLES
    S,              \* FIFO queue of unexplored states
    C,              \* set of explored (seen) states
    state,          \* the state currently being processed
    successors,     \* unexplored successors of state
    T,              \* set of <<predecessor, successor>> pairs
    L,              \* map from states to their BFS levels
    counterexample, \* the error trace being built
    pc              \* program counter

vars == <<S, C, state, successors, T, L, counterexample, pc>>

-----------------------------------------------------------------------------
(* Helper definitions *)

Initials == StateGraph.initials

SuccessorsOf(s) == {t \in StateGraph.states : <<s, t>> \in StateGraph.actions}

Range(f) == {f[x] : x \in DOMAIN f}

IsInjective(f) == \A a, b \in DOMAIN f : f[a] = f[b] => a = b

\* All permutations of a finite set, represented as sequences.
SetToSeqs(set) ==
    {f \in [1..Cardinality(set) -> set] : IsInjective(f)}

ConstrainedInits == {s \in Initials : Constraint(s, 0)}

Min(a, b) == IF a <= b THEN a ELSE b

RemoveAt(seq, i) == SubSeq(seq, 1, i - 1) \o SubSeq(seq, i + 1, Len(seq))

Null == CHOOSE x : x \notin StateGraph.states

\* The predecessor of t recorded in T.
Predecessor(t) == (CHOOSE p \in T : p[2] = t)[1]

-----------------------------------------------------------------------------
Init ==
    /\ S \in SetToSeqs(ConstrainedInits)
    /\ C = {}
    /\ state = Null
    /\ successors = {}
    /\ T = {}
    /\ L = [s \in ConstrainedInits |-> 0]
    /\ counterexample = <<>>
    /\ pc = "init_chk"

(* Check the initial states for violations. *)
InitCheck ==
    /\ pc = "init_chk"
    /\ IF \E s \in Range(S) : s \in ViolationStates
          THEN /\ counterexample' =
                    <<CHOOSE s \in Range(S) : s \in ViolationStates>>
               /\ pc' = "Done"
               /\ C' = C
          ELSE /\ C' = Range(S)
               /\ pc' = "deq"
               /\ UNCHANGED counterexample
    /\ UNCHANGED <<S, state, successors, T, L>>

(* Dequeue one of the first K states of the queue. A state without     *)
(* successors (deadlock) simply yields nothing to explore.             *)
Dequeue ==
    /\ pc = "deq"
    /\ IF S # <<>>
          THEN \E i \in 1..Min(K, Len(S)) :
                 /\ state' = S[i]
                 /\ S' = RemoveAt(S, i)
                 /\ successors' =
                      {t \in SuccessorsOf(S[i]) \ C :
                          Constraint(t, L[S[i]] + 1)}
                 /\ pc' = "expl"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<S, state, successors>>
    /\ UNCHANGED <<C, T, L, counterexample>>

(* Explore one unexplored successor of the current state. *)
Explore ==
    /\ pc = "expl"
    /\ IF successors # {}
          THEN \E t \in successors :
                 /\ successors' = successors \ {t}
                 /\ C' = C \cup {t}
                 /\ T' = T \cup {<<state, t>>}
                 /\ L' = L @@ (t :> L[state] + 1)
                 /\ S' = Append(S, t)
                 /\ IF t \in ViolationStates
                       THEN /\ counterexample' = <<t>>
                            /\ pc' = "trc"
                       ELSE /\ pc' = "expl"
                            /\ UNCHANGED counterexample
          ELSE /\ pc' = "deq"
               /\ UNCHANGED <<successors, C, T, L, S, counterexample>>
    /\ UNCHANGED state

(* Reconstruct the counterexample back to an initial state. *)
Trace ==
    /\ pc = "trc"
    /\ IF Head(counterexample) \notin Initials
          THEN /\ counterexample' =
                    <<Predecessor(Head(counterexample))>> \o counterexample
               /\ pc' = "trc"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED counterexample
    /\ UNCHANGED <<S, C, state, successors, T, L>>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == InitCheck \/ Dequeue \/ Explore \/ Trace \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(InitCheck)
    /\ WF_vars(Dequeue)
    /\ WF_vars(Explore)
    /\ WF_vars(Trace)

-----------------------------------------------------------------------------
(* Safety *)

TypeOK ==
    /\ S \in Seq(StateGraph.states)
    /\ C \subseteq StateGraph.states
    /\ state \in StateGraph.states \cup {Null}
    /\ successors \subseteq StateGraph.states
    /\ T \subseteq StateGraph.actions
    /\ counterexample \in Seq(StateGraph.states)
    /\ pc \in {"init_chk", "deq", "expl", "trc", "Done"}

\* Every recorded pair is an edge of the graph, and the trace (once
\* complete) is a path from an initial state ending in a violation.
IsPath(seq) ==
    \A i \in 1..(Len(seq) - 1) : <<seq[i], seq[i + 1]>> \in StateGraph.actions

Inv ==
    /\ \A p \in T : p \in StateGraph.actions
    /\ (pc = "Done" /\ counterexample # <<>>) =>
          /\ Head(counterexample) \in Initials
          /\ counterexample[Len(counterexample)] \in ViolationStates
          /\ IsPath(counterexample)

-----------------------------------------------------------------------------
(* Liveness *)

Termination == <>(pc = "Done")

MinLen ==
    CHOOSE n \in {Len(c) : c \in Counterexamples} :
        \A c \in Counterexamples : n <= Len(c)

Live ==
    (ViolationStates \cap StateGraph.states # {}) =>
        <>[](/\ pc = "Done"
             /\ counterexample \in Counterexamples
             /\ (K = 1 => Len(counterexample) = MinLen))

-----------------------------------------------------------------------------
(* Refinement of a set-based, nondeterministic reachability exploration   *)
(* (MCReachability).  The abstract spec is given over parameters so the   *)
(* refinement mapping can be stated by substitution.                      *)

ReachInit(visited, frontier) ==
    /\ visited = ConstrainedInits
    /\ frontier = ConstrainedInits

ReachNext(visited, frontier, visitedP, frontierP) ==
    \E s \in frontier :
        \/ \E t \in SuccessorsOf(s) \ visited :
              /\ visitedP = visited \cup {t}
              /\ frontierP = frontier \cup {t}
        \/ /\ visitedP = visited
           /\ frontierP = frontier \ {s}

\* Refinement mapping
RVisited == C \cup Range(S)
RFrontier == Range(S) \cup (IF pc \in {"expl", "trc"} THEN {state} ELSE {})

Refinement ==
    /\ ReachInit(RVisited, RFrontier)
    /\ [][ReachNext(RVisited, RFrontier, RVisited', RFrontier')]_<<RVisited, RFrontier>>

THEOREM Spec => []TypeOK /\ []Inv /\ Termination /\ Live /\ Refinement
=============================================================================