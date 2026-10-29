------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

Procs == 0 .. (N - 1)

\* Fork indices: the right fork of philosopher p is fork p,
\* the left fork of philosopher p is fork (p + 1) % N.
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

\* Philosophers 1..N-1 take right then left; philosopher 0 takes left then right.
FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

(* --algorithm DiningPhilosophers
variables sem = [f \in Procs |-> 1];

fair+ process Philosopher \in Procs
begin
  Think:
    while TRUE do
      GetFirst:
        await sem[FirstFork(self)] = 1;
        sem[FirstFork(self)] := 0;
      GetSecond:
        await sem[SecondFork(self)] = 1;
        sem[SecondFork(self)] := 0;
      Eat:
        sem[FirstFork(self)] := 1;
      ReleaseSecond:
        sem[SecondFork(self)] := 1;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES sem, pc

vars == << sem, pc >>

ProcSet == Procs

Init == /\ sem = [f \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "Think"]

Think(self) == /\ pc[self] = "Think"
               /\ pc' = [pc EXCEPT ![self] = "GetFirst"]
               /\ sem' = sem

GetFirst(self) == /\ pc[self] = "GetFirst"
                  /\ sem[FirstFork(self)] = 1
                  /\ sem' = [sem EXCEPT ![FirstFork(self)] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "GetSecond"]

GetSecond(self) == /\ pc[self] = "GetSecond"
                   /\ sem[SecondFork(self)] = 1
                   /\ sem' = [sem EXCEPT ![SecondFork(self)] = 0]
                   /\ pc' = [pc EXCEPT ![self] = "Eat"]

Eat(self) == /\ pc[self] = "Eat"
             /\ sem' = [sem EXCEPT ![FirstFork(self)] = 1]
             /\ pc' = [pc EXCEPT ![self] = "ReleaseSecond"]

ReleaseSecond(self) == /\ pc[self] = "ReleaseSecond"
                       /\ sem' = [sem EXCEPT ![SecondFork(self)] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "Think"]

Philosopher(self) == \/ Think(self)
                     \/ GetFirst(self)
                     \/ GetSecond(self)
                     \/ Eat(self)
                     \/ ReleaseSecond(self)

Next == \E self \in Procs : Philosopher(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(Philosopher(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ sem \in [Procs -> {0, 1}]
          /\ pc \in [Procs -> {"Think", "GetFirst", "GetSecond", "Eat", "ReleaseSecond"}]

\* Two neighbouring philosophers (which share a fork) never eat at the same time.
EatingInvariant ==
    \A p \in Procs :
        ~ (pc[p] = "Eat" /\ pc[LeftFork(p)] = "Eat")

\* Every philosopher that tries to eat eventually eats (starvation freedom).
StarvationFree ==
    \A p \in Procs : (pc[p] = "GetFirst") ~> (pc[p] = "Eat")

=============================================================================