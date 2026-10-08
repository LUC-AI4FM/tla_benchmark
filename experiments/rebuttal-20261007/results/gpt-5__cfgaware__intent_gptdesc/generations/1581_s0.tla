---- MODULE DiningPhilosophers ----
EXTENDS Naturals, Sequences

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
  Indexing:
  - Philosophers and forks are both indexed by 0..N-1.
  - Fork f sits between philosophers f and Succ(f).
  - Philosopher i needs forks Left(i) and Right(i) to eat, where
      Left(i) = IF i = 0 THEN N-1 ELSE i-1
      Right(i) = i
*)

Philos == 0..(N-1)
Forks  == Philos

Null == "NoOwner"

Succ(i) == IF i = N-1 THEN 0 ELSE i + 1
Left(i) == IF i = 0 THEN N - 1 ELSE i - 1
Right(i) == i

VARIABLES phase, owner

vars == << phase, owner >>

TypeOK ==
  /\ phase \in [Philos -> {"Thinking", "Hungry", "Eating"}]
  /\ owner \in [Forks  -> (Philos \cup {Null})]

Holds(i, f) == owner[f] = i
BothHeld(i) == Holds(i, Left(i)) /\ Holds(i, Right(i))

Init ==
  /\ phase = [i \in Philos |-> "Thinking"]
  /\ owner = [f \in Forks  |-> Null]

(*
  Actions for philosopher i:
  - BeginHungry: Thinking -> Hungry
  - TakeLeft/TakeRight: take one free adjacent fork while Hungry
  - TakeBoth: atomically take both free forks while Hungry
  - StartEat: transition to Eating once both forks are held
  - StopEat: release both forks and return to Thinking
  - Backoff: while Hungry, release any held fork(s) to avoid deadlock
*)

BeginHungry(i) ==
  /\ i \in Philos
  /\ phase[i] = "Thinking"
  /\ phase' = [phase EXCEPT ![i] = "Hungry"]
  /\ UNCHANGED owner

TakeLeft(i) ==
  /\ i \in Philos
  /\ phase[i] = "Hungry"
  /\ owner[Left(i)] = Null
  /\ owner' = [owner EXCEPT ![Left(i)] = i]
  /\ UNCHANGED phase

TakeRight(i) ==
  /\ i \in Philos
  /\ phase[i] = "Hungry"
  /\ owner[Right(i)] = Null
  /\ owner' = [owner EXCEPT ![Right(i)] = i]
  /\ UNCHANGED phase

TakeBoth(i) ==
  /\ i \in Philos
  /\ phase[i] = "Hungry"
  /\ owner[Left(i)] = Null
  /\ owner[Right(i)] = Null
  /\ owner' = [owner EXCEPT ![Left(i)] = i, ![Right(i)] = i]
  /\ UNCHANGED phase

StartEat(i) ==
  /\ i \in Philos
  /\ phase[i] = "Hungry"
  /\ BothHeld(i)
  /\ phase' = [phase EXCEPT ![i] = "Eating"]
  /\ UNCHANGED owner

StopEat(i) ==
  /\ i \in Philos
  /\ phase[i] = "Eating"
  /\ phase' = [phase EXCEPT ![i] = "Thinking"]
  /\ owner' =
       [owner
         EXCEPT
           ![Left(i)]  = IF owner[Left(i)]  = i THEN Null ELSE @,
           ![Right(i)] = IF owner[Right(i)] = i THEN Null ELSE @
       ]

Backoff(i) ==
  /\ i \in Philos
  /\ phase[i] = "Hungry"
  /\ (owner[Left(i)] = i \/ owner[Right(i)] = i)
  /\ owner' =
       [owner
         EXCEPT
           ![Left(i)]  = IF owner[Left(i)]  = i THEN Null ELSE @,
           ![Right(i)] = IF owner[Right(i)] = i THEN Null ELSE @
       ]
  /\ UNCHANGED phase

HungryStep(i) ==
  TakeBoth(i) \/ TakeLeft(i) \/ TakeRight(i) \/ StartEat(i) \/ Backoff(i)

Next ==
  \E i \in Philos :
       BeginHungry(i)
    \/ HungryStep(i)
    \/ StopEat(i)

(*
  Safety properties (as a state invariant):
    - TypeOK
    - Mutual exclusion on forks
    - If Eating then both forks are held
    - No two adjacent philosophers eat simultaneously
*)

ForkMutualExcl ==
  \A f \in Forks :
    \A i, j \in Philos :
      i # j => ~(owner[f] = i /\ owner[f] = j)

EatingHasForks ==
  \A i \in Philos : phase[i] = "Eating" => BothHeld(i)

AdjacentNoEat ==
  \A i \in Philos : ~(phase[i] = "Eating" /\ phase[Succ(i)] = "Eating")

Invariant ==
  TypeOK /\ ForkMutualExcl /\ EatingHasForks /\ AdjacentNoEat

(*
  Liveness assumptions (fair scheduling and progress while Hungry):
    - Each philosopher makes progress while Hungry (strong fairness over HungryStep)
    - A philosopher does not eat forever without releasing (weak fairness over StopEat)
*)

Fairness ==
  /\ \A i \in Philos : SF_vars(HungryStep(i))
  /\ \A i \in Philos : WF_vars(StopEat(i))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

(*
  Strong starvation freedom requirement:
    - Whenever a philosopher is Hungry, they will eventually reach Eating.
*)
StarvationFree ==
  \A i \in Philos : [](phase[i] = "Hungry" => <> (phase[i] = "Eating"))

====