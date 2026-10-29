------------------------------- MODULE TLCMC -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Inputs, given as overridable definitions.                               *)
(* StateGraph is a record [states, initials, actions], where actions maps  *)
(* each state to its set of successor states.                              *)
(***************************************************************************)
StateGraph ==
    [ states   |-> {1, 2, 3, 4},
      initials |-> {1},
      actions  |-> [ s \in {1, 2, 3, 4} |->
                       CASE s = 1 -> {2, 3}
                         [] s = 2 -> {4}
                         [] s = 3 -> {4}
                         [] OTHER -> {1} ] ]

ViolationStates == {4}

null == "null"

\* Window parameter: how many queue-head positions may be dequeued.
K == 1

\* Pruning predicate on a state and its BFS level.
Constraint(s, lvl) == TRUE

\* Known counterexamples, possibly empty, used for liveness reasoning.
KnownCounterexamples == {}

States   == StateGraph.states
Initials == StateGraph.initials
Succ(s)  == StateGraph.actions[s]

Min(a, b) == IF a < b THEN a ELSE b

IsDeadlock(s) == Succ(s) \subseteq {s}

ASSUME /\ Initials \subseteq States
       /\ ViolationStates \subseteq States
       /\ \A s \in States : Succ(s) \subseteq States
       /\ null \notin States
       /\ K \in Nat \ {0}

(***************************************************************************)
(* Variables.                                                              *)
(*  S              : set of discovered (seen) states                       *)
(*  C              : predecessor map, state -> predecessor or null         *)
(*  L              : BFS level map, state -> level                         *)
(*  T              : queue of discovered but unexplored states             *)
(*  state          : state currently being expanded                        *)
(*  successors     : pending initial states or pending successors          *)
(*  i              : BFS level of the current state                        *)
(*  counterexample : reported path, or <<>>                                *)
(*  pc             : control location                                      *)
(***************************************************************************)
VARIABLES S, C, L, T, state, successors, i, counterexample, pc

vars == <<S, C, L, T, state, successors, i, counterexample, pc>>

\* Build the path back to an initial state by following the predecessor map.
RECURSIVE TraceOf(_, _, _)
TraceOf(s, Cm, n) ==
    IF n = 0 \/ Cm[s] = null
    THEN <<s>>
    ELSE Append(TraceOf(Cm[s], Cm, n - 1), s)

Trace(s, Cm) == TraceOf(s, Cm, Cardinality(States))

TypeOK ==
    /\ S \subseteq States
    /\ C \in [States -> States \cup {null}]
    /\ L \in [States -> Nat]
    /\ T \in Seq(States)
    /\ state \in States \cup {null}
    /\ successors \subseteq States
    /\ i \in Nat
    /\ counterexample \in Seq(States)
    /\ pc \in {"init", "loop", "expand", "done"}

Init ==
    /\ S = {}
    /\ C = [s \in States |-> null]
    /\ L = [s \in States |-> 0]
    /\ T = <<>>
    /\ state = null
    /\ successors = Initials
    /\ i = 0
    /\ counterexample = <<>>
    /\ pc = "init"

(* Initial states are processed in any order. *)
InitStep ==
    /\ pc = "init"
    /\ IF successors = {}
       THEN /\ pc' = "loop"
            /\ UNCHANGED <<S, C, L, T, state, successors, i, counterexample>>
       ELSE \E s \in successors :
              /\ successors' = successors \ {s}
              /\ UNCHANGED <<C, state, i>>
              /\ IF ~Constraint(s, 0) \/ s \in S
                 THEN UNCHANGED <<S, L, T, counterexample, pc>>
                 ELSE IF s \in ViolationStates
                      THEN /\ S' = S \cup {s}
                           /\ L' = [L EXCEPT ![s] = 0]
                           /\ counterexample' = <<s>>
                           /\ pc' = "done"
                           /\ UNCHANGED T
                      ELSE /\ S' = S \cup {s}
                           /\ L' = [L EXCEPT ![s] = 0]
                           /\ T' = Append(T, s)
                           /\ UNCHANGED <<counterexample, pc>>

(* Nondeterministically pick one of the first min(K, Len(T)) queue entries. *)
Dequeue ==
    /\ pc = "loop"
    /\ IF T = <<>>
       THEN /\ pc' = "done"
            /\ UNCHANGED <<S, C, L, T, state, successors, i, counterexample>>
       ELSE \E j \in 1..Min(K, Len(T)) :
              LET s == T[j] IN
              /\ T' = SubSeq(T, 1, j - 1) \o SubSeq(T, j + 1, Len(T))
              /\ state' = s
              /\ i' = L[s]
              /\ UNCHANGED <<S, C, L>>
              /\ IF IsDeadlock(s)
                 THEN /\ counterexample' = Trace(s, C)
                      /\ pc' = "done"
                      /\ successors' = {}
                 ELSE /\ successors' = {t \in Succ(s) : Constraint(t, L[s] + 1)}
                      /\ pc' = "expand"
                      /\ UNCHANGED counterexample

(* Process the successors of the current state one at a time. *)
Expand ==
    /\ pc = "expand"
    /\ IF successors = {}
       THEN /\ pc' = "loop"
            /\ UNCHANGED <<S, C, L, T, state, successors, i, counterexample>>
       ELSE \E t \in successors :
              /\ successors' = successors \ {t}
              /\ UNCHANGED <<state, i>>
              /\ IF t \in S
                 THEN UNCHANGED <<S, C, L, T, counterexample, pc>>
                 ELSE /\ S' = S \cup {t}
                      /\ C' = [C EXCEPT ![t] = state]
                      /\ L' = [L EXCEPT ![t] = i + 1]
                      /\ IF t \in ViolationStates
                         THEN /\ counterexample' = Trace(t, C')
                              /\ pc' = "done"
                              /\ UNCHANGED T
                         ELSE /\ T' = Append(T, t)
                              /\ UNCHANGED <<counterexample, pc>>

Terminating == pc = "done" /\ UNCHANGED vars

Next == InitStep \/ Dequeue \/ Expand \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
IsPath(p) ==
    /\ Len(p) >= 1
    /\ \A k \in 1..(Len(p) - 1) : p[k + 1] \in Succ(p[k])

Last(p) == p[Len(p)]

\* Safety: a reported counterexample is a valid path from an initial state
\* to a violation or deadlock state.
Safety ==
    counterexample # <<>> =>
        /\ IsPath(counterexample)
        /\ counterexample[1] \in Initials
        /\ (Last(counterexample) \in ViolationStates
            \/ IsDeadlock(Last(counterexample)))

\* States reachable within n steps, through states satisfying the predicate.
RECURSIVE ReachN(_)
ReachN(n) ==
    IF n = 0
    THEN {s \in Initials : Constraint(s, 0)}
    ELSE ReachN(n - 1) \cup
         {t \in UNION {Succ(s) : s \in ReachN(n - 1)} : Constraint(t, n)}

Levels == 0..Cardinality(States)

ViolationReachable == \E n \in Levels : ReachN(n) \cap ViolationStates # {}

MinViolationLen ==
    IF ViolationReachable
    THEN 1 + (CHOOSE n \in Levels :
                /\ ReachN(n) \cap ViolationStates # {}
                /\ \A m \in Levels : m < n => ReachN(m) \cap ViolationStates = {})
    ELSE 0

\* BFS minimality when K = 1.
Minimality ==
    (K = 1 /\ counterexample # <<>> /\ Last(counterexample) \in ViolationStates)
        => Len(counterexample) = MinViolationLen

Inv == TypeOK /\ Safety /\ Minimality

\* Completeness modulo pruning.
Completeness == ViolationReachable => <>(counterexample # <<>>)

\* Termination: exploration ends; without a counterexample the queue is empty.
Termination == <>(pc = "done" /\ (counterexample = <<>> => T = <<>>))

\* Liveness with respect to the known counterexamples.
Live ==
    KnownCounterexamples # {} =>
        <>[](/\ counterexample \in KnownCounterexamples
             /\ (K = 1 => \A ce \in KnownCounterexamples :
                             Len(counterexample) <= Len(ce)))

\* Refinement of an abstract checker: a counterexample, once reported, never changes.
Refinement ==
    [][counterexample # <<>> => counterexample' = counterexample]_vars

=============================================================================