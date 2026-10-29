---------------------------- MODULE BFS ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    StateGraph,       \* [states |-> ..., initials |-> ..., actions |-> ...]
    ViolationStates,  \* states that violate the checked property
    null,             \* marker for "no predecessor"
    K,                \* K = 1: strict BFS, K > 1: non-strict BFS (multiple workers)
    Counterexample    \* set of known (valid) counterexamples

States   == StateGraph.states
Initials == StateGraph.initials
Actions  == StateGraph.actions

ASSUME StateGraphAssumption ==
    /\ {"states", "initials", "actions"} \subseteq DOMAIN StateGraph
    /\ Initials \subseteq States
    /\ Actions \subseteq (States \X States)

ASSUME KAssumption == K \in Nat \ {0}
ASSUME NullAssumption == null \notin States
ASSUME ViolationAssumption == ViolationStates \subseteq States
ASSUME CounterexampleAssumption == Counterexample \subseteq Seq(States)

Succs(s) == { t \in States : <<s, t>> \in Actions }

Min(a, b) == IF a <= b THEN a ELSE b

RemoveAt(seq, j) == SubSeq(seq, 1, j - 1) \o SubSeq(seq, j + 1, Len(seq))

-----------------------------------------------------------------------------
(* Translation of the PlusCal algorithm *)

VARIABLES
    S,              \* set of explored states
    C,              \* queue of pending (unexplored) states
    T,              \* predecessor function: state -> predecessor (or null)
    L,              \* BFS level function: state -> level
    successors,     \* successors of the state currently being explored
    cur,            \* state currently being explored
    inits,          \* initial states not yet processed
    counterexample, \* the reconstructed counterexample
    pc              \* program counter

vars == <<S, C, T, L, successors, cur, inits, counterexample, pc>>

Init ==
    /\ S = {}
    /\ C = <<>>
    /\ T = [s \in {} |-> null]
    /\ L = [s \in {} |-> 0]
    /\ successors = {}
    /\ cur = null
    /\ inits = Initials
    /\ counterexample = <<>>
    /\ pc = "init"

(* Process initial states. *)
InitStep ==
    /\ pc = "init"
    /\ IF inits # {}
         THEN \E s \in inits :
                /\ inits' = inits \ {s}
                /\ IF s \notin S
                     THEN /\ S' = S \cup {s}
                          /\ C' = Append(C, s)
                          /\ T' = T @@ (s :> null)
                          /\ L' = L @@ (s :> 0)
                          /\ IF s \in ViolationStates
                               THEN /\ counterexample' = <<s>>
                                    /\ pc' = "trc"
                               ELSE UNCHANGED <<counterexample, pc>>
                     ELSE UNCHANGED <<S, C, T, L, counterexample, pc>>
                /\ UNCHANGED <<successors, cur>>
         ELSE /\ pc' = "while"
              /\ UNCHANGED <<S, C, T, L, successors, cur, inits, counterexample>>

(* Dequeue one of the first K states (strict BFS when K = 1). *)
WhileStep ==
    /\ pc = "while"
    /\ IF C # <<>>
         THEN \E j \in 1..Min(K, Len(C)) :
                /\ cur' = C[j]
                /\ C' = RemoveAt(C, j)
                /\ successors' = Succs(C[j])
                /\ pc' = "inner"
                /\ UNCHANGED <<S, T, L, inits, counterexample>>
         ELSE /\ pc' = "Done"
              /\ UNCHANGED <<S, C, T, L, successors, cur, inits, counterexample>>

(* Explore the successors of the current state. *)
InnerStep ==
    /\ pc = "inner"
    /\ IF successors # {}
         THEN \E t \in successors :
                /\ successors' = successors \ {t}
                /\ IF t \notin S
                     THEN /\ S' = S \cup {t}
                          /\ C' = Append(C, t)
                          /\ T' = T @@ (t :> cur)
                          /\ L' = L @@ (t :> L[cur] + 1)
                          /\ IF t \in ViolationStates
                               THEN /\ counterexample' = <<t>>
                                    /\ pc' = "trc"
                               ELSE UNCHANGED <<counterexample, pc>>
                     ELSE UNCHANGED <<S, C, T, L, counterexample, pc>>
                /\ UNCHANGED <<cur, inits>>
         ELSE /\ pc' = "while"
              /\ UNCHANGED <<S, C, T, L, successors, cur, inits, counterexample>>

(* Reconstruct the counterexample by following predecessors. *)
TraceStep ==
    /\ pc = "trc"
    /\ IF T[Head(counterexample)] = null
         THEN /\ pc' = "Done"
              /\ UNCHANGED counterexample
         ELSE /\ counterexample' = <<T[Head(counterexample)]>> \o counterexample
              /\ UNCHANGED pc
    /\ UNCHANGED <<S, C, T, L, successors, cur, inits>>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == InitStep \/ WhileStep \/ InnerStep \/ TraceStep \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ S \subseteq States
    /\ C \in Seq(States)
    /\ DOMAIN T = S
    /\ \A s \in S : T[s] \in States \cup {null}
    /\ DOMAIN L = S
    /\ \A s \in S : L[s] \in Nat
    /\ successors \subseteq States
    /\ cur \in States \cup {null}
    /\ inits \subseteq Initials
    /\ counterexample \in Seq(States)
    /\ pc \in {"init", "while", "inner", "trc", "Done"}

QueueExplored == \A j \in 1..Len(C) : C[j] \in S

PredecessorValid ==
    \A s \in S : T[s] # null => /\ T[s] \in S
                                /\ <<T[s], s>> \in Actions
                                /\ L[s] = L[T[s]] + 1

CounterexampleValid ==
    pc = "Done" /\ counterexample # <<>> =>
        /\ counterexample[1] \in Initials
        /\ counterexample[Len(counterexample)] \in ViolationStates
        /\ \A j \in 1..(Len(counterexample) - 1) :
              <<counterexample[j], counterexample[j + 1]>> \in Actions

-----------------------------------------------------------------------------
(* Liveness properties *)

Termination == <>(pc = "Done")

MinLength ==
    CHOOSE n \in { Len(c) : c \in Counterexample } :
        \A c \in Counterexample : n <= Len(c)

Live ==
    (ViolationStates # {} /\ Counterexample # {}) =>
        <>[]( /\ pc = "Done"
              /\ counterexample \in Counterexample
              /\ (K = 1 => Len(counterexample) = MinLength) )

-----------------------------------------------------------------------------
(* Refinement mapping to the (inlined) MCReachability specification:   *)
(* the abstract reachable set is mapped to the explored set S.          *)

Reach == S

RInit == Reach = {}

RNext == \E s \in Initials \cup UNION { Succs(r) : r \in Reach } :
            /\ s \notin Reach
            /\ S' = Reach \cup {s}

RSpec == RInit /\ [][RNext]_S

Refinement == RSpec

THEOREM Spec => []TypeOK
THEOREM Spec => Termination
THEOREM Spec => Live
THEOREM Spec => Refinement
=============================================================================