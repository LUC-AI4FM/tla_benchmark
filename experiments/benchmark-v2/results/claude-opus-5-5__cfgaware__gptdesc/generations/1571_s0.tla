---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Philosophers == 0 .. (N - 1)

\* Philosopher p's right fork is fork p; its left fork is fork (p+1) % N.
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

(* --algorithm DiningPhilosophers
variables forks = [f \in 0..(N-1) |-> 1];

define
  P(s) == forks[s] = 1
end define;

process Phil \in 0..(N-1)
variables first = IF self = 0 THEN LeftFork(self) ELSE RightFork(self),
          second = IF self = 0 THEN RightFork(self) ELSE LeftFork(self);
begin
Think:
  while TRUE do
    GetFirst:
      await forks[first] = 1;
      forks[first] := 0;
    GetSecond:
      await forks[second] = 1;
      forks[second] := 0;
    Eat:
      skip;
    Release:
      forks[first] := 1 || forks[second] := 1;
  end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES forks, pc

vars == << forks, pc >>

ProcSet == Philosophers

First(self)  == IF self = 0 THEN LeftFork(self) ELSE RightFork(self)
Second(self) == IF self = 0 THEN RightFork(self) ELSE LeftFork(self)

Init == /\ forks = [f \in Philosophers |-> 1]
        /\ pc = [self \in ProcSet |-> "Think"]

Think(self) == /\ pc[self] = "Think"
               /\ pc' = [pc EXCEPT ![self] = "GetFirst"]
               /\ UNCHANGED forks

GetFirst(self) == /\ pc[self] = "GetFirst"
                  /\ forks[First(self)] = 1
                  /\ forks' = [forks EXCEPT ![First(self)] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "GetSecond"]

GetSecond(self) == /\ pc[self] = "GetSecond"
                   /\ forks[Second(self)] = 1
                   /\ forks' = [forks EXCEPT ![Second(self)] = 0]
                   /\ pc' = [pc EXCEPT ![self] = "Eat"]

Eat(self) == /\ pc[self] = "Eat"
             /\ pc' = [pc EXCEPT ![self] = "Release"]
             /\ UNCHANGED forks

Release(self) == /\ pc[self] = "Release"
                 /\ forks' = [forks EXCEPT ![First(self)] = 1,
                                           ![Second(self)] = 1]
                 /\ pc' = [pc EXCEPT ![self] = "Think"]

Phil(self) == Think(self) \/ GetFirst(self) \/ GetSecond(self)
              \/ Eat(self) \/ Release(self)

Next == \E self \in Philosophers : Phil(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Philosophers : SF_vars(Phil(self))
\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ forks \in [Philosophers -> {0, 1}]
          /\ pc \in [Philosophers -> {"Think", "GetFirst", "GetSecond", "Eat", "Release"}]

Eating(p) == pc[p] = "Eat"

\* Two neighbouring philosophers never eat at the same time.
Invariant == /\ TypeOK
             /\ \A p \in Philosophers : Eating(p) => ~Eating((p + 1) % N)

\* Every philosopher that tries to eat eventually eats.
StarvationFreedom == \A p \in Philosophers :
                        (pc[p] = "GetFirst") ~> (pc[p] = "Eat")

Liveness == \A p \in Philosophers : []<>(pc[p] = "Eat")

=============================================================================