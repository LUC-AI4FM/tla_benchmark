----------------------------- MODULE DiningPhilosophers -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    N,        \* number of philosophers/forks, N \in Nat, N >= 2
    None      \* special value denoting that a fork is free; None ∉ 0..N-1

ASSUME N \in Nat /\ N >= 2
ASSUME None \notin 0..(N - 1)

(***************************************************************************)
(* Sets and basic definitions                                              *)
(***************************************************************************)

Philosophers == 0..(N - 1)
Forks        == 0..(N - 1)

States == {"Thinking", "Hungry", "Eating"}

LeftFork(i)  == IF i = 0 THEN N - 1 ELSE i - 1
RightFork(i) == i
Succ(i)      == IF i = N - 1 THEN 0 ELSE i + 1

(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)

VARIABLES
    phase,       \* [Philosophers -> States]
    forkOwner    \* [Forks -> (Philosophers \cup {None})]

vars == << phase, forkOwner >>

(***************************************************************************)
(* Typing invariant                                                        *)
(***************************************************************************)

TypeInv ==
    /\ phase \in [Philosophers -> States]
    /\ forkOwner \in [Forks -> Philosophers \cup {None}]

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)

Init ==
    /\ phase = [ i \in Philosophers |-> "Thinking" ]
    /\ forkOwner = [ f \in Forks |-> None ]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

DecideToEat(i) ==
    /\ i \in Philosophers
    /\ phase[i] = "Thinking"
    /\ phase' = [phase EXCEPT ![i] = "Hungry"]
    /\ UNCHANGED forkOwner

TakeLeft(i) ==
    /\ i \in Philosophers
    /\ phase[i] = "Hungry"
    /\ LET l == LeftFork(i) IN forkOwner[l] = None
    /\ LET l == LeftFork(i) IN forkOwner' = [forkOwner EXCEPT ![l] = i]
    /\ UNCHANGED phase

TakeRight(i) ==
    /\ i \in Philosophers
    /\ phase[i] = "Hungry"
    /\ LET r == RightFork(i) IN forkOwner[r] = None
    /\ LET r == RightFork(i) IN forkOwner' = [forkOwner EXCEPT ![r] = i]
    /\ UNCHANGED phase

StartEating(i) ==
    /\ i \in Philosophers
    /\ phase[i] = "Hungry"
    /\ LET l == LeftFork(i)  IN forkOwner[l] = i
    /\ LET r == RightFork(i) IN forkOwner[r] = i
    /\ phase' = [phase EXCEPT ![i] = "Eating"]
    /\ UNCHANGED forkOwner

FinishEat(i) ==
    /\ i \in Philosophers
    /\ phase[i] = "Eating"
    /\ phase' = [phase EXCEPT ![i] = "Thinking"]
    /\ LET l == LeftFork(i)  IN
       LET r == RightFork(i) IN
         forkOwner' = [forkOwner EXCEPT ![l] = None, ![r] = None]

(***************************************************************************)
(* Global next-state relation                                              *)
(***************************************************************************)

Next ==
    \E i \in Philosophers:
        DecideToEat(i)
      \/ TakeLeft(i)
      \/ TakeRight(i)
      \/ StartEating(i)
      \/ FinishEat(i)

(***************************************************************************)
(* Fairness assumptions (progress of scheduling and enabled actions)       *)
(***************************************************************************)

Fairness ==
    /\ \A i \in Philosophers: SF_vars(TakeLeft(i))
    /\ \A i \in Philosophers: SF_vars(TakeRight(i))
    /\ \A i \in Philosophers: WF_vars(StartEating(i))
    /\ \A i \in Philosophers: WF_vars(FinishEat(i))
    /\ \A i \in Philosophers: SF_vars(DecideToEat(i))

(***************************************************************************)
(* Full behavior specification                                             *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* No two adjacent philosophers may be eating simultaneously.
AdjacentNotEating ==
    \A i \in Philosophers:
        ~(phase[i] = "Eating" /\ phase[Succ(i)] = "Eating")

\* Mutual exclusion on forks: each fork is held by at most one philosopher.
UniqueForkOwnership ==
    \A f \in Forks:
        LET owners == { i \in Philosophers : forkOwner[f] = i } IN
            Cardinality(owners) <= 1

\* If a philosopher is Eating, they must hold both adjacent forks.
EatingHasBoth ==
    \A i \in Philosophers:
        phase[i] = "Eating" =>
            /\ forkOwner[LeftFork(i)]  = i
            /\ forkOwner[RightFork(i)] = i

Safety == TypeInv /\ AdjacentNotEating /\ UniqueForkOwnership /\ EatingHasBoth

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* Any attempt to eat (becoming Hungry) eventually leads to Eating.
AttemptLeadsToEat(i) ==
    i \in Philosophers => (phase[i] = "Hungry") ~> (phase[i] = "Eating")

AttemptLeadsToEatAll ==
    \A i \in Philosophers: AttemptLeadsToEat(i)

\* Strong starvation-freedom: each philosopher infinitely often enters Eating.
StarvationFreedom(i) ==
    i \in Philosophers => []<>(phase[i] = "Eating")

StarvationFreedomAll ==
    \A i \in Philosophers: StarvationFreedom(i)

\* Deadlock freedom: in all reachable states, some action is enabled.
NoGlobalDeadlock ==
    [](ENABLED Next)

================================================================================