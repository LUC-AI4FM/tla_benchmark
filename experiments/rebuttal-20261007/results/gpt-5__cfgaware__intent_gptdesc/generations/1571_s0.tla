------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Integers

CONSTANT N

(*
  Philosophers and forks are indexed 0..N-1 around a circle.
  We require N >= 2 to model two distinct adjacent forks per philosopher.
*)
ASSUME N \in Nat /\ N >= 2

Philos == 0..(N - 1)
Forks  == 0..(N - 1)

NoOwner == "None"

PhaseVals == {"Think", "Hungry", "Eat"}

Succ(i) == IF i = N - 1 THEN 0 ELSE i + 1
Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

LeftFork(i)  == i
RightFork(i) == Pred(i)

VARIABLES
  phase,      \* function from philosopher -> phase in PhaseVals
  forkOwner   \* function from fork -> philosopher or NoOwner

vars == << phase, forkOwner >>

Init ==
  /\ phase \in [Philos -> PhaseVals]
  /\ \A i \in Philos: phase[i] = "Think"
  /\ forkOwner \in [Forks -> (Philos \cup {NoOwner})]
  /\ \A f \in Forks: forkOwner[f] = NoOwner

ThinkToHungry(i) ==
  /\ i \in Philos
  /\ phase[i] = "Think"
  /\ phase' = [phase EXCEPT ![i] = "Hungry"]
  /\ UNCHANGED forkOwner

TakeLeft(i) ==
  /\ i \in Philos
  /\ phase[i] = "Hungry"
  /\ forkOwner[LeftFork(i)] = NoOwner
  /\ forkOwner' = [forkOwner EXCEPT ![LeftFork(i)] = i]
  /\ UNCHANGED phase

TakeRight(i) ==
  /\ i \in Philos
  /\ phase[i] = "Hungry"
  /\ forkOwner[RightFork(i)] = NoOwner
  /\ forkOwner' = [forkOwner EXCEPT ![RightFork(i)] = i]
  /\ UNCHANGED phase

StartEating(i) ==
  /\ i \in Philos
  /\ phase[i] = "Hungry"
  /\ forkOwner[LeftFork(i)] = i
  /\ forkOwner[RightFork(i)] = i
  /\ phase' = [phase EXCEPT ![i] = "Eat"]
  /\ UNCHANGED forkOwner

StopEating(i) ==
  /\ i \in Philos
  /\ phase[i] = "Eat"
  /\ phase' = [phase EXCEPT ![i] = "Think"]
  /\ forkOwner' =
       [forkOwner EXCEPT
          ![LeftFork(i)]  = NoOwner,
          ![RightFork(i)] = NoOwner]

Next ==
  \E i \in Philos:
       ThinkToHungry(i)
    \/ TakeLeft(i)
    \/ TakeRight(i)
    \/ StartEating(i)
    \/ StopEating(i)

TypeOK ==
  /\ phase \in [Philos -> PhaseVals]
  /\ forkOwner \in [Forks -> (Philos \cup {NoOwner})]

MutualExclusion ==
  \A i \in Philos:
    ~(phase[i] = "Eat" /\ phase[Succ(i)] = "Eat")

EatingHasBothForks ==
  \A i \in Philos:
    phase[i] = "Eat"
      => /\ forkOwner[LeftFork(i)] = i
         /\ forkOwner[RightFork(i)] = i

ThinkHoldsNoFork ==
  \A i \in Philos:
    phase[i] = "Think"
      => /\ forkOwner[LeftFork(i)]  # i
         /\ forkOwner[RightFork(i)] # i

ForkUniqueOwner ==
  \A f \in Forks:
    \A i, j \in Philos:
      i # j => ~(forkOwner[f] = i /\ forkOwner[f] = j)

ResourceIntegrity ==
  /\ EatingHasBothForks
  /\ ThinkHoldsNoFork
  /\ ForkUniqueOwner

Invariant ==
  /\ TypeOK
  /\ MutualExclusion
  /\ ResourceIntegrity

Fairness ==
  /\ \A i \in Philos:
        /\ WF_vars(ThinkToHungry(i))
        /\ WF_vars(TakeLeft(i))
        /\ WF_vars(TakeRight(i))
        /\ SF_vars(StartEating(i))
        /\ WF_vars(StopEating(i))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

(*
  Additional temporal properties that can be checked against Spec:
*)

DeadlockFree ==
  [] (ENABLED Next)

StarvationFreedom ==
  \A i \in Philos: []<>(phase[i] = "Eat")

=============================================================================