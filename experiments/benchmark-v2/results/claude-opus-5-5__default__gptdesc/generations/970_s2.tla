------------------------------- MODULE BFSModelChecker -------------------------------
(***************************************************************************)
(* A TLC-like reachability model checker performing (possibly non-strict)  *)
(* breadth-first search over an explicitly given state graph.              *)
(*                                                                         *)
(* K = 1  : strict BFS. The head of the queue is always dequeued.          *)
(* K > 1  : degraded BFS. Any of the first K queue elements may be         *)
(*          dequeued, which approximates K concurrent workers.             *)
(*                                                                         *)
(* The checker tracks explored states S, the pending queue C, predecessor  *)
(* information pred, and BFS levels L. It uses them to detect violations   *)
(* and to reconstruct counterexamples.                                     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    StateGraph,       \* [states |-> ..., initials |-> ..., actions |-> ...]
    ViolationStates,  \* set of states violating the checked invariant
    Counterexamples,  \* set of known (valid) counterexample behaviours
    K                 \* degree of non-strictness of the BFS (K = 1 : strict)

ASSUME /\ K \in Nat \ {0}
       /\ StateGraph.initials \subseteq StateGraph.states
       /\ StateGraph.actions \subseteq (StateGraph.states \X StateGraph.states)
       /\ ViolationStates \subseteq StateGraph.states
       /\ IsFiniteSet(StateGraph.states)

VARIABLES
    S,              \* set of explored (seen) states
    C,              \* queue (sequence) of pending states
    s,              \* state currently being expanded
    succs,          \* successors of s that still have to be processed
    pred,           \* predecessor of each discovered state
    L,              \* BFS level of each discovered state
    counterexample, \* reconstructed counterexample (<<>> if none)
    pc              \* program counter of the translated PlusCal algorithm

vars == << S, C, s, succs, pred, L, counterexample, pc >>

States   == StateGraph.states
Initials == StateGraph.initials
Actions  == StateGraph.actions

NoState == CHOOSE x : x \notin States

Min(a, b) == IF a <= b THEN a ELSE b

SetToSeq(X) ==
    CHOOSE f \in [1..Cardinality(X) -> X] :
        \A i, j \in DOMAIN f : f[i] = f[j] => i = j

RemoveAt(seq, j) == SubSeq(seq, 1, j - 1) \o SubSeq(seq, j + 1, Len(seq))

Successors(x) == { t \in States : <<x, t>> \in Actions }

(* Counterexample reconstruction by following predecessor links back to   *)
(* an initial state.                                                       *)
RECURSIVE Trace(_)
Trace(t) == IF t \in Initials \/ pred[t] = NoState
              THEN << t >>
              ELSE Append(Trace(pred[t]), t)

---------------------------------------------------------------------------------------
(***************************************************************************)
(* Translated PlusCal algorithm                                            *)
(***************************************************************************)

Init ==
    /\ S = {}
    /\ C = << >>
    /\ s = NoState
    /\ succs = {}
    /\ pred = [x \in States |-> NoState]
    /\ L = [x \in States |-> 0]
    /\ counterexample = << >>
    /\ pc = "init"

(* Check the initial states and initialise the queue. *)
init ==
    /\ pc = "init"
    /\ S' = Initials
    /\ L' = [x \in States |-> 0]
    /\ IF Initials \cap ViolationStates # {}
         THEN /\ counterexample' = << CHOOSE v \in Initials \cap ViolationStates : TRUE >>
              /\ C' = << >>
              /\ pc' = "Done"
         ELSE /\ C' = SetToSeq(Initials)
              /\ pc' = "deq"
              /\ UNCHANGED counterexample
    /\ UNCHANGED << s, succs, pred >>

(* Dequeue one of the first K states of the queue. *)
deq ==
    /\ pc = "deq"
    /\ IF C = << >>
         THEN /\ pc' = "Done"
              /\ UNCHANGED << C, s, succs >>
         ELSE \E j \in 1..Min(K, Len(C)) :
                /\ s' = C[j]
                /\ C' = RemoveAt(C, j)
                /\ succs' = Successors(C[j]) \ S
                /\ pc' = "exp"
    /\ UNCHANGED << S, pred, L, counterexample >>

(* Expand the current state one successor at a time. *)
exp ==
    /\ pc = "exp"
    /\ IF succs = {}
         THEN /\ pc' = "deq"
              /\ UNCHANGED << S, C, succs, pred, L, counterexample >>
         ELSE \E t \in succs :
                /\ succs' = succs \ {t}
                /\ IF t \in S
                     THEN /\ UNCHANGED << S, C, pred, L, counterexample >>
                          /\ pc' = "exp"
                     ELSE /\ S' = S \cup {t}
                          /\ C' = Append(C, t)
                          /\ pred' = [pred EXCEPT ![t] = s]
                          /\ L' = [L EXCEPT ![t] = L[s] + 1]
                          /\ IF t \in ViolationStates
                               THEN /\ counterexample' =
                                         Append(LET RECURSIVE Tr(_)
                                                    Tr(x) == IF x \in Initials \/ pred[x] = NoState
                                                               THEN << x >>
                                                               ELSE Append(Tr(pred[x]), x)
                                                IN Tr(s), t)
                                    /\ pc' = "Done"
                               ELSE /\ UNCHANGED counterexample
                                    /\ pc' = "exp"
    /\ UNCHANGED s

Terminating == pc = "Done" /\ UNCHANGED vars

Next == init \/ deq \/ exp \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------------------
(***************************************************************************)
(* Safety                                                                  *)
(***************************************************************************)

TypeOK ==
    /\ S \subseteq States
    /\ C \in Seq(States)
    /\ s \in States \cup {NoState}
    /\ succs \subseteq States
    /\ pred \in [States -> States \cup {NoState}]
    /\ L \in [States -> Nat]
    /\ counterexample \in Seq(States)
    /\ pc \in {"init", "deq", "exp", "Done"}

(* Every queued state has been explored. *)
QueueExplored == \A j \in 1..Len(C) : C[j] \in S

(* Explored, non-initial states have a predecessor one BFS level lower. *)
PredConsistent ==
    \A t \in S \ Initials :
        /\ pred[t] \in S
        /\ <<pred[t], t>> \in Actions
        /\ L[t] = L[pred[t]] + 1

(* A reported counterexample is a genuine path into a violation state. *)
CounterexampleValid ==
    counterexample # << >> =>
        /\ counterexample[1] \in Initials
        /\ counterexample[Len(counterexample)] \in ViolationStates
        /\ \A j \in 1..(Len(counterexample) - 1) :
              <<counterexample[j], counterexample[j + 1]>> \in Actions

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)

Termination == <>(pc = "Done")

MinLength == CHOOSE n \in { Len(ce) : ce \in Counterexamples } :
                 \A ce \in Counterexamples : n <= Len(ce)

Live ==
    (ViolationStates # {}) =>
        <>[]( /\ pc = "Done"
              /\ counterexample \in Counterexamples
              /\ (K = 1 => Len(counterexample) = MinLength) )

---------------------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to the MCReachability specification.                 *)
(* MCReachability is inlined here as an abstract set of explored states    *)
(* growing by successors of already explored states.                       *)
(***************************************************************************)

MCReach_Init(explored) == explored = Initials

MCReach_Next(explored, explored2) ==
    \E u \in explored, t \in States :
        /\ <<u, t>> \in Actions
        /\ explored2 = explored \cup {t}

exploredBar == IF pc = "init" THEN Initials ELSE S

MCReachability_Spec ==
    /\ MCReach_Init(exploredBar)
    /\ [][MCReach_Next(exploredBar, exploredBar')]_exploredBar

THEOREM Spec => []TypeOK /\ []CounterexampleValid /\ Termination /\ MCReachability_Spec

=======================================================================================