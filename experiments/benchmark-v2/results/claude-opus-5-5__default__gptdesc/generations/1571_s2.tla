------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

Procs == 0 .. N-1

\* Fork indices: philosopher p sits between fork p (right) and fork (p+1) % N (left)
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

\* Philosopher 0 picks up its left fork first; the others pick up their right fork first
FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

(* --algorithm DiningPhilosophers
variables fork = [k \in Procs |-> 1];

macro P(s) begin
  await fork[s] > 0;
  fork[s] := fork[s] - 1;
end macro;

macro V(s) begin
  fork[s] := fork[s] + 1;
end macro;

fair+ process Phil \in Procs
begin
  think:
    while TRUE do
      first:
        P(FirstFork(self));
      second:
        P(SecondFork(self));
      eat:
        skip;
      releaseFirst:
        V(SecondFork(self));
      releaseSecond:
        V(FirstFork(self));
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES fork, pc

vars == << fork, pc >>

ProcSet == Procs

Init == /\ fork = [k \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "think"]

think(self) == /\ pc[self] = "think"
               /\ pc' = [pc EXCEPT ![self] = "first"]
               /\ fork' = fork

first(self) == /\ pc[self] = "first"
               /\ fork[FirstFork(self)] > 0
               /\ fork' = [fork EXCEPT ![FirstFork(self)] = fork[FirstFork(self)] - 1]
               /\ pc' = [pc EXCEPT ![self] = "second"]

second(self) == /\ pc[self] = "second"
                /\ fork[SecondFork(self)] > 0
                /\ fork' = [fork EXCEPT ![SecondFork(self)] = fork[SecondFork(self)] - 1]
                /\ pc' = [pc EXCEPT ![self] = "eat"]

eat(self) == /\ pc[self] = "eat"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "releaseFirst"]
             /\ fork' = fork

releaseFirst(self) == /\ pc[self] = "releaseFirst"
                      /\ fork' = [fork EXCEPT ![SecondFork(self)] = fork[SecondFork(self)] + 1]
                      /\ pc' = [pc EXCEPT ![self] = "releaseSecond"]

releaseSecond(self) == /\ pc[self] = "releaseSecond"
                       /\ fork' = [fork EXCEPT ![FirstFork(self)] = fork[FirstFork(self)] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "think"]

Phil(self) == think(self) \/ first(self) \/ second(self) \/ eat(self)
                \/ releaseFirst(self) \/ releaseSecond(self)

Next == (\E self \in Procs : Phil(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(Phil(self))
\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ fork \in [Procs -> {0, 1}]
          /\ pc \in [Procs -> {"think", "first", "second", "eat",
                               "releaseFirst", "releaseSecond"}]

\* A philosopher is eating once it holds both forks and has not yet released any
Eating(p) == pc[p] \in {"eat", "releaseFirst"}

\* Mutual exclusion: two neighbouring philosophers (who share a fork) never eat at the same time
MutualExclusion ==
    \A p \in Procs : ~(Eating(p) /\ Eating((p + 1) % N))

\* Starvation freedom: every philosopher that becomes hungry eventually eats
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "first") ~> (pc[p] = "eat")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFreedom
=============================================================================