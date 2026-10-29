---------------------------- MODULE TLCMC ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    StateGraph,        \* [states |-> ..., initials |-> ..., actions |-> [states -> SUBSET states]]
    ViolationStates,   \* states violating the safety property
    K,                 \* window size (number of workers) for non-strict BFS
    Constraint(_, _),  \* Constraint(s, level): state constraint at BFS level
    Counterexample     \* set of known valid counterexamples (sequences of states)

States   == StateGraph.states
Initials == StateGraph.initials
Actions  == StateGraph.actions

ASSUME /\ K \in Nat \ {0}
       /\ Initials \subseteq States
       /\ Actions \in [States -> SUBSET States]
       /\ ViolationStates \subseteq States

Min(a, b) == IF a < b THEN a ELSE b

----------------------------------------------------------------------------
\* Graph helpers used by the properties

RECURSIVE ReachN(_)
ReachN(n) == IF n = 0 THEN Initials
             ELSE ReachN(n - 1) \cup UNION {Actions[s] : s \in ReachN(n - 1)}

Reachable == ReachN(Cardinality(States))

Deadlocks == {s \in Reachable : Actions[s] \ {s} = {}}

NoConstraint ==
    \A s \in States, l \in 0..Cardinality(States) : Constraint(s, l)

IsPath(p) ==
    /\ Len(p) > 0
    /\ p[1] \in Initials
    /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Actions[p[i]]

IsCE(p) == IsPath(p) /\ p[Len(p)] \in ViolationStates

ShortestLen ==
    CHOOSE n \in 1..(Cardinality(States) + 1) :
        /\ ReachN(n - 1) \cap ViolationStates # {}
        /\ \A m \in 1..(n - 1) : ReachN(m - 1) \cap ViolationStates = {}

----------------------------------------------------------------------------
VARIABLES
    S,              \* set of visited (seen) states
    C,              \* predecessor map: C[s] = parent of s (roots map to themselves)
    Q,              \* BFS queue of <<state, level>>
    inits,          \* initial states not yet checked
    state,          \* state currently being explored
    lvl,            \* BFS level of the current state
    succs,          \* remaining successors of current state to process
    T,              \* cursor used for trace reconstruction
    counterexample, \* the reconstructed counterexample trace
    pc              \* control location

vars == <<S, C, Q, inits, state, lvl, succs, T, counterexample, pc>>

AddParent(f, x, y) == [z \in DOMAIN f \cup {x} |-> IF z = x THEN y ELSE f[z]]

Init ==
    /\ S = {}
    /\ C = [x \in {} |-> x]
    /\ Q = <<>>
    /\ inits = Initials
    /\ state = CHOOSE s \in States : TRUE
    /\ lvl = 0
    /\ succs = {}
    /\ T = CHOOSE s \in States : TRUE
    /\ counterexample = <<>>
    /\ pc = "init"

\* Check initial states one at a time, before any successor exploration.
InitStep ==
    /\ pc = "init"
    /\ IF inits = {}
         THEN /\ pc' = "deq"
              /\ UNCHANGED <<S, C, Q, inits, state, lvl, succs, T, counterexample>>
         ELSE \E s \in inits :
                /\ inits' = inits \ {s}
                /\ IF ~Constraint(s, 0)
                     THEN UNCHANGED <<S, C, Q, state, lvl, succs, T, counterexample, pc>>
                     ELSE /\ S' = S \cup {s}
                          /\ C' = AddParent(C, s, s)
                          /\ IF s \in ViolationStates
                               THEN /\ T' = s
                                    /\ pc' = "trc"
                                    /\ Q' = Q
                               ELSE /\ Q' = Append(Q, <<s, 0>>)
                                    /\ UNCHANGED <<T, pc>>
                          /\ UNCHANGED <<state, lvl, succs, counterexample>>

\* Dequeue any of the first K elements (K = 1 is strict BFS).
Deq ==
    /\ pc = "deq"
    /\ IF Q = <<>>
         THEN /\ pc' = "done"
              /\ UNCHANGED <<S, C, Q, inits, state, lvl, succs, T, counterexample>>
         ELSE \E i \in 1..Min(K, Len(Q)) :
                LET s  == Q[i][1]
                    l  == Q[i][2]
                    ss == Actions[s] \ {s}
                IN  /\ Q' = SubSeq(Q, 1, i - 1) \o SubSeq(Q, i + 1, Len(Q))
                    /\ state' = s
                    /\ lvl' = l
                    /\ succs' = ss
                    /\ IF ss = {}
                         THEN /\ T' = s          \* deadlock
                              /\ pc' = "trc"
                         ELSE /\ T' = T
                              /\ pc' = "each"
                    /\ UNCHANGED <<S, C, inits, counterexample>>

\* Process the successors of the current state.
Each ==
    /\ pc = "each"
    /\ IF succs = {}
         THEN /\ pc' = "deq"
              /\ UNCHANGED <<S, C, Q, inits, state, lvl, succs, T, counterexample>>
         ELSE \E t \in succs :
                /\ succs' = succs \ {t}
                /\ IF t \in S \/ ~Constraint(t, lvl + 1)
                     THEN UNCHANGED <<S, C, Q, T, pc>>
                     ELSE /\ S' = S \cup {t}
                          /\ C' = AddParent(C, t, state)
                          /\ IF t \in ViolationStates
                               THEN /\ T' = t
                                    /\ pc' = "trc"
                                    /\ Q' = Q
                               ELSE /\ Q' = Append(Q, <<t, lvl + 1>>)
                                    /\ UNCHANGED <<T, pc>>
                /\ UNCHANGED <<inits, state, lvl, counterexample>>

\* Reconstruct the counterexample by following predecessor links.
Trc ==
    /\ pc = "trc"
    /\ counterexample' = <<T>> \o counterexample
    /\ IF C[T] = T
         THEN /\ pc' = "done"
              /\ T' = T
         ELSE /\ T' = C[T]
              /\ pc' = pc
    /\ UNCHANGED <<S, C, Q, inits, state, lvl, succs>>

Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == InitStep \/ Deq \/ Each \/ Trc \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ S \subseteq States
    /\ DOMAIN C = S
    /\ \A s \in S : C[s] \in S
    /\ inits \subseteq Initials
    /\ succs \subseteq States
    /\ pc \in {"init", "deq", "each", "trc", "done"}

\* All initial states are checked before successors are explored.
InitsFirst == pc \in {"deq", "each"} => inits = {}

\* Every explored state is marked visited before its successors are processed.
ExploredVisited == pc = "each" => state \in S

\* No state is enqueued (hence explored) twice.
QueueVisited == \A i \in 1..Len(Q) : Q[i][1] \in S
NoDuplicates ==
    \A i, j \in 1..Len(Q) : i # j => Q[i][1] # Q[j][1]

\* Completion without violation implies empty frontier.
DoneEmptyQueue == (pc = "done" /\ counterexample = <<>>) => Q = <<>>

\* Any produced trace is a valid path from an initial state.
TraceIsPath == (pc = "done" /\ counterexample # <<>>) => IsPath(counterexample)

\* Strict BFS yields a shortest counterexample to a violation state.
ShortestCE ==
    (K = 1 /\ pc = "done" /\ counterexample # <<>>
           /\ counterexample[Len(counterexample)] \in ViolationStates
           /\ NoConstraint)
        => Len(counterexample) = ShortestLen

----------------------------------------------------------------------------
\* Liveness properties

Termination == <>(pc = "done")

CounterexampleLiveness ==
    (Reachable \cap ViolationStates # {}
        /\ Deadlocks \ ViolationStates = {}
        /\ NoConstraint)
      => <>( /\ pc = "done"
             /\ counterexample \in Counterexample
             /\ IsCE(counterexample)
             /\ (K = 1 => Len(counterexample) = ShortestLen))

=============================================================================