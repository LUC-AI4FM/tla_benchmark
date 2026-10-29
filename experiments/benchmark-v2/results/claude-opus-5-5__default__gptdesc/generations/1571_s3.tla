---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, Integers

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

Procs == 0..(N-1)

\* Fork p is the right fork of philosopher p.
\* Fork (p+1) % N is the left fork of philosopher p.
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

\* Philosophers 1..N-1 take the right fork first, then the left fork.
\* Philosopher 0 takes the left fork first, then the right fork.
FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

(* --algorithm DiningPhilosophers
variables fork = [f \in Procs |-> 1];

fair+ process Phil \in Procs
begin
Think:
  while TRUE do
    skip;
  GetFirst:
    await fork[FirstFork(self)] = 1;
    fork[FirstFork(self)] := fork[FirstFork(self)] - 1;
  GetSecond:
    await fork[SecondFork(self)] = 1;
    fork[SecondFork(self)] := fork[SecondFork(self)] - 1;
  Eat:
    skip;
  Release:
    fork := [fork EXCEPT ![FirstFork(self)]  = @ + 1,
                         ![SecondFork(self)] = @ + 1];
  end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES fork, pc

vars == << fork, pc >>

ProcSet == Procs

Init == /\ fork = [f \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "Think"]

Think(self) == /\ pc[self] = "Think"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "GetFirst"]
               /\ fork' = fork

GetFirst(self) == /\ pc[self] = "GetFirst"
                  /\ fork[FirstFork(self)] = 1
                  /\ fork' = [fork EXCEPT ![FirstFork(self)] = fork[FirstFork(self)] - 1]
                  /\ pc' = [pc EXCEPT ![self] = "GetSecond"]

GetSecond(self) == /\ pc[self] = "GetSecond"
                   /\ fork[SecondFork(self)] = 1
                   /\ fork' = [fork EXCEPT ![SecondFork(self)] = fork[SecondFork(self)] - 1]
                   /\ pc' = [pc EXCEPT ![self] = "Eat"]

Eat(self) == /\ pc[self] = "Eat"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Release"]
             /\ fork' = fork

Release(self) == /\ pc[self] = "Release"
                 /\ fork' = [fork EXCEPT ![FirstFork(self)]  = @ + 1,
                                         ![SecondFork(self)] = @ + 1]
                 /\ pc' = [pc EXCEPT ![self] = "Think"]

Phil(self) == Think(self) \/ GetFirst(self) \/ GetSecond(self)
                \/ Eat(self) \/ Release(self)

Next == (\E self \in Procs : Phil(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(Phil(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
\* Type correctness
TypeOK == /\ fork \in [Procs -> {0, 1}]
          /\ pc \in [Procs -> {"Think", "GetFirst", "GetSecond", "Eat", "Release"}]

\* Mutual-exclusion-style eating invariant: two neighbouring philosophers
\* (who share a fork) never eat at the same time.
Eating(p) == pc[p] = "Eat"

MutualExclusion ==
    \A p \in Procs : Eating(p) => ~Eating((p + 1) % N)

\* Starvation freedom: every philosopher that wants to eat eventually eats.
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "GetFirst") ~> (pc[p] = "Eat")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFreedom
=============================================================================