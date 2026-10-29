---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

Procs == 0 .. N-1

RightFork(p) == p
LeftFork(p)  == (p + 1) % N

LeftNeighbor(p)  == (p + N - 1) % N
RightNeighbor(p) == (p + 1) % N

(* --algorithm DiningPhilosophers
variables fork = [k \in Procs |-> 1];

define
  P(s, k) == fork[k] > 0
end define;

fair+ process Phil \in Procs
begin
  Think:
    while TRUE do
      First:
        if self = 0 then
          await fork[LeftFork(self)] > 0;
          fork[LeftFork(self)] := fork[LeftFork(self)] - 1;
        else
          await fork[RightFork(self)] > 0;
          fork[RightFork(self)] := fork[RightFork(self)] - 1;
        end if;
      Second:
        if self = 0 then
          await fork[RightFork(self)] > 0;
          fork[RightFork(self)] := fork[RightFork(self)] - 1;
        else
          await fork[LeftFork(self)] > 0;
          fork[LeftFork(self)] := fork[LeftFork(self)] - 1;
        end if;
      Eat:
        skip;
      ReleaseFirst:
        fork[LeftFork(self)] := fork[LeftFork(self)] + 1;
      ReleaseSecond:
        fork[RightFork(self)] := fork[RightFork(self)] + 1;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES fork, pc

vars == << fork, pc >>

ProcSet == Procs

Init == /\ fork = [k \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "Think"]

Think(self) == /\ pc[self] = "Think"
               /\ pc' = [pc EXCEPT ![self] = "First"]
               /\ UNCHANGED fork

First(self) == /\ pc[self] = "First"
               /\ IF self = 0
                     THEN /\ fork[LeftFork(self)] > 0
                          /\ fork' = [fork EXCEPT ![LeftFork(self)] = fork[LeftFork(self)] - 1]
                     ELSE /\ fork[RightFork(self)] > 0
                          /\ fork' = [fork EXCEPT ![RightFork(self)] = fork[RightFork(self)] - 1]
               /\ pc' = [pc EXCEPT ![self] = "Second"]

Second(self) == /\ pc[self] = "Second"
                /\ IF self = 0
                      THEN /\ fork[RightFork(self)] > 0
                           /\ fork' = [fork EXCEPT ![RightFork(self)] = fork[RightFork(self)] - 1]
                      ELSE /\ fork[LeftFork(self)] > 0
                           /\ fork' = [fork EXCEPT ![LeftFork(self)] = fork[LeftFork(self)] - 1]
                /\ pc' = [pc EXCEPT ![self] = "Eat"]

Eat(self) == /\ pc[self] = "Eat"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "ReleaseFirst"]
             /\ UNCHANGED fork

ReleaseFirst(self) == /\ pc[self] = "ReleaseFirst"
                      /\ fork' = [fork EXCEPT ![LeftFork(self)] = fork[LeftFork(self)] + 1]
                      /\ pc' = [pc EXCEPT ![self] = "ReleaseSecond"]

ReleaseSecond(self) == /\ pc[self] = "ReleaseSecond"
                       /\ fork' = [fork EXCEPT ![RightFork(self)] = fork[RightFork(self)] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "Think"]

Phil(self) == \/ Think(self)
              \/ First(self)
              \/ Second(self)
              \/ Eat(self)
              \/ ReleaseFirst(self)
              \/ ReleaseSecond(self)

Next == \E self \in Procs : Phil(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(Phil(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK ==
  /\ fork \in [Procs -> {0, 1}]
  /\ pc \in [Procs -> {"Think", "First", "Second", "Eat",
                       "ReleaseFirst", "ReleaseSecond"}]

Eating(p) == pc[p] = "Eat"

\* Mutual-exclusion-style eating invariant: neighbours never eat simultaneously
EatingInvariant ==
  \A p \in Procs : Eating(p) => ~Eating(RightNeighbor(p)) /\ ~Eating(LeftNeighbor(p))

\* Starvation freedom: every hungry philosopher eventually eats
StarvationFreedom ==
  \A p \in Procs : (pc[p] = "First") ~> (pc[p] = "Eat")

=============================================================================