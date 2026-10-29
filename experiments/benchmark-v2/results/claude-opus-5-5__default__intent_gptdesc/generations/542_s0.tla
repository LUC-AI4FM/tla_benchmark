---------------------------- MODULE TwoWorkerCounter ----------------------------
(***************************************************************************)
(* Two independent concurrent workers each perform a single increment on  *)
(* a shared integer counter. Each worker's update is one indivisible      *)
(* state transition. The scheduler may pick either ready worker at each   *)
(* step. After both workers finish, the system idles forever.             *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS Workers            \* the set of worker identifiers

ASSUME WorkersCard == /\ IsFiniteSet(Workers)
                      /\ Cardinality(Workers) = 2

VARIABLES counter,           \* the shared integer counter
          pc                 \* pc[w] \in {"ready", "done"}

vars == <<counter, pc>>

-----------------------------------------------------------------------------
(* Initial state: counter is zero and both workers are ready.             *)
Init == /\ counter = 0
        /\ pc = [w \in Workers |-> "ready"]

(* A worker performs its single increment and becomes finished.           *)
Increment(w) == /\ pc[w] = "ready"
                /\ counter' = counter + 1
                /\ pc' = [pc EXCEPT ![w] = "done"]

AllDone == \A w \in Workers : pc[w] = "done"

(* Once both workers are finished, the system may idle forever.           *)
Idle == /\ AllDone
        /\ UNCHANGED vars

Next == \/ \E w \in Workers : Increment(w)
        \/ Idle

(* Weak fairness on each worker's increment step.                         *)
Fairness == \A w \in Workers : WF_vars(Increment(w))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*************************** Safety properties *****************************)

TypeOK == /\ counter \in Int
          /\ counter \in Nat
          /\ pc \in [Workers -> {"ready", "done"}]

(* The counter is always an integer (invariant).                          *)
CounterIsInt == counter \in Int

(* The counter never decreases.                                           *)
CounterNonDecreasing == [][counter' >= counter]_counter

(* Every worker step increases the counter by exactly one.                *)
WorkerStepIncrementsByOne ==
    [][\A w \in Workers :
          (pc[w] = "ready" /\ pc'[w] = "done") => counter' = counter + 1]_vars

(* The only state changes are worker increments; no spontaneous changes   *)
(* to the counter (or any other variable) occur.                          *)
OnlyWorkerChanges ==
    [][\E w \in Workers : Increment(w)]_vars

(* The counter always equals the number of workers that have finished.    *)
CounterMatchesFinished ==
    counter = Cardinality({w \in Workers : pc[w] = "done"})

(* In any final state, the counter equals the number of workers (two).    *)
FinalCounterCorrect ==
    AllDone => counter = Cardinality(Workers)

FinalCounterIsTwo ==
    AllDone => counter = 2

-----------------------------------------------------------------------------
(*************************** Liveness properties ***************************)

(* Eventually both workers reach their finished state.                    *)
Termination == <>AllDone

(* Every individual worker eventually finishes.                           *)
EachWorkerFinishes == \A w \in Workers : <>(pc[w] = "done")

(* Eventually, and forever after, the counter equals two.                 *)
EventuallyCounterTwo == <>[](counter = 2)

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ CounterIsInt /\ CounterMatchesFinished
                   /\ FinalCounterCorrect /\ FinalCounterIsTwo)
THEOREM Spec => CounterNonDecreasing /\ WorkerStepIncrementsByOne
                /\ OnlyWorkerChanges
THEOREM Spec => Termination /\ EachWorkerFinishes /\ EventuallyCounterTwo
=============================================================================