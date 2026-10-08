--------------------------- MODULE ChandyMisraDP ---------------------------

EXTENDS Naturals, TLC

(*
Dining Philosophers (Chandy-Misra) in PlusCal, with NP philosophers seated
in a circle and NP forks indexed by 0..NP-1, where fork j sits between
philosophers j and (j+1) mod NP. Each philosopher i has:
- left fork index = i
- right fork index = IF i = 0 THEN NP-1 ELSE i-1
Initial state:
- Every fork is dirty and held by the lower-numbered adjacent philosopher,
  except fork 2 which is held by philosopher 1.
- Every philosopher starts hungry = TRUE.

Loop step (per philosopher, weakly fair):
- If holding a dirty left (resp. right) fork, clean it and pass it to the
  left (resp. right) neighbor.
- Else if hungry and holding both forks and both are clean, go to Eat.
- Else if not hungry, go to Think.
Eat step:
- Set hungry := FALSE; mark both held forks dirty.
Think step:
- Set hungry := TRUE.
*)

CONSTANT NP

ASSUME NP \in Nat /\ NP >= 3

P == 0..(NP - 1)

Inc(i) == IF i = NP - 1 THEN 0 ELSE i + 1
Dec(i) == IF i = 0 THEN NP - 1 ELSE i - 1

LeftFork(i)  == i
RightFork(i) == Dec(i)

LeftNeighbor(i)  == Inc(i)
RightNeighbor(i) == Dec(i)

LowerOf(a, b) == IF a < b THEN a ELSE b

VARIABLES forks, hungry, pc

vars == << forks, hungry, pc >>

ForkInit ==
  [ j \in P |-> [ holder |-> IF j = 2 THEN 1 ELSE LowerOf(j, Inc(j)),
                  clean  |-> FALSE ] ]

Init ==
  /\ forks = ForkInit
  /\ hungry = [ i \in P |-> TRUE ]
  /\ pc = [ i \in P |-> "Loop" ]

HoldsLeft(i)  == forks[LeftFork(i)].holder = i
HoldsRight(i) == forks[RightFork(i)].holder = i
CleanLeft(i)  == forks[LeftFork(i)].clean
CleanRight(i) == forks[RightFork(i)].clean

LoopPassLeft(i) ==
  /\ pc[i] = "Loop"
  /\ HoldsLeft(i)
  /\ ~CleanLeft(i)
  /\ forks' =
       [ forks EXCEPT
           ![LeftFork(i)] = [ @ EXCEPT !.holder = LeftNeighbor(i), !.clean = TRUE ] ]
  /\ UNCHANGED << hungry, pc >>

LoopPassRight(i) ==
  /\ pc[i] = "Loop"
  /\ HoldsRight(i)
  /\ ~CleanRight(i)
  /\ forks' =
       [ forks EXCEPT
           ![RightFork(i)] = [ @ EXCEPT !.holder = RightNeighbor(i), !.clean = TRUE ] ]
  /\ UNCHANGED << hungry, pc >>

LoopGoEat(i) ==
  /\ pc[i] = "Loop"
  /\ hungry[i]
  /\ HoldsLeft(i) /\ HoldsRight(i)
  /\ CleanLeft(i) /\ CleanRight(i)
  /\ pc' = [pc EXCEPT ![i] = "Eat"]
  /\ UNCHANGED << forks, hungry >>

EatStep(i) ==
  /\ pc[i] = "Eat"
  /\ hungry' = [hungry EXCEPT ![i] = FALSE]
  /\ forks' =
       [ forks EXCEPT
           ![LeftFork(i)]  = [ @ EXCEPT !.holder = i, !.clean = FALSE ],
           ![RightFork(i)] = [ @ EXCEPT !.holder = i, !.clean = FALSE ] ]
  /\ pc' = [pc EXCEPT ![i] = "Loop"]

LoopGoThink(i) ==
  /\ pc[i] = "Loop"
  /\ ~hungry[i]
  /\ pc' = [pc EXCEPT ![i] = "Think"]
  /\ UNCHANGED << forks, hungry >>

ThinkStep(i) ==
  /\ pc[i] = "Think"
  /\ hungry' = [hungry EXCEPT ![i] = TRUE]
  /\ forks' = forks
  /\ pc' = [pc EXCEPT ![i] = "Loop"]

ProcNext(i) ==
     LoopPassLeft(i)
  \/ LoopPassRight(i)
  \/ LoopGoEat(i)
  \/ EatStep(i)
  \/ LoopGoThink(i)
  \/ ThinkStep(i)

Next ==
  \E i \in P: ProcNext(i)

Spec ==
  Init /\ [][Next]_vars /\ \A i \in P: WF_vars(ProcNext(i))

TypeOK ==
  /\ forks \in [ P -> [ holder: P, clean: BOOLEAN ] ]
  /\ hungry \in [ P -> BOOLEAN ]
  /\ pc \in [ P -> { "Loop", "Eat", "Think" } ]

ExclusiveAccess ==
  \A i \in P: ~(pc[i] = "Eat" /\ pc[Inc(i)] = "Eat")

NobodyStarves ==
  \A i \in P: []<>(pc[i] = "Eat")

============================================================================