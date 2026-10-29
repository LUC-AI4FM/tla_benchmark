------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

Procs == 0 .. (N - 1)

LeftFork(p)  == p
RightFork(p) == (p + 1) % N

(* Philosophers 1..N-1 take the right fork first, then the left fork.   *)
(* Philosopher 0 takes them in the opposite order (left first, then     *)
(* right), breaking the symmetric deadlock.                             *)
FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

(***************************************************************************
--algorithm DiningPhilosophers {
    variable fork = [f \in Procs |-> 1];

    fair+ process (Phil \in Procs) {
      Think:
        while (TRUE) {
          Hungry1:
            await fork[FirstFork(self)] = 1;
            fork[FirstFork(self)] := 0;
          Hungry2:
            await fork[SecondFork(self)] = 1;
            fork[SecondFork(self)] := 0;
          Eat:
            fork[FirstFork(self)] := 1 ||
            fork[SecondFork(self)] := 1;
        }
    }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES fork, pc

vars == << fork, pc >>

ProcSet == Procs

Init == /\ fork = [f \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "Think"]

Think(self) == /\ pc[self] = "Think"
               /\ pc' = [pc EXCEPT ![self] = "Hungry1"]
               /\ UNCHANGED fork

Hungry1(self) == /\ pc[self] = "Hungry1"
                 /\ fork[FirstFork(self)] = 1
                 /\ fork' = [fork EXCEPT ![FirstFork(self)] = 0]
                 /\ pc' = [pc EXCEPT ![self] = "Hungry2"]

Hungry2(self) == /\ pc[self] = "Hungry2"
                 /\ fork[SecondFork(self)] = 1
                 /\ fork' = [fork EXCEPT ![SecondFork(self)] = 0]
                 /\ pc' = [pc EXCEPT ![self] = "Eat"]

Eat(self) == /\ pc[self] = "Eat"
             /\ fork' = [fork EXCEPT ![FirstFork(self)] = 1,
                                     ![SecondFork(self)] = 1]
             /\ pc' = [pc EXCEPT ![self] = "Think"]

Phil(self) == Think(self) \/ Hungry1(self) \/ Hungry2(self) \/ Eat(self)

Next == \E self \in Procs : Phil(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(Phil(self))
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Properties *)

TypeOK == /\ fork \in [Procs -> {0, 1}]
          /\ pc \in [Procs -> {"Think", "Hungry1", "Hungry2", "Eat"}]

Eating(p) == pc[p] = "Eat"

(* Mutual exclusion: two neighbouring philosophers never eat at the same time. *)
NoNeighborsEat ==
    \A p \in Procs : ~(Eating(p) /\ Eating(RightFork(p)))

(* Every fork is held by at most one philosopher, consistent with semaphore. *)
HoldsFork(p, f) ==
    \/ (pc[p] \in {"Hungry2", "Eat"} /\ f = FirstFork(p))
    \/ (pc[p] = "Eat" /\ f = SecondFork(p))

ForkExclusion ==
    \A f \in Procs :
        /\ Cardinality({p \in Procs : HoldsFork(p, f)}) <= 1
        /\ (fork[f] = 0) <=> (\E p \in Procs : HoldsFork(p, f))

Safety == TypeOK /\ NoNeighborsEat /\ ForkExclusion

(* Starvation freedom: every hungry philosopher eventually eats, *)
(* and every philosopher eats infinitely often.                  *)
StarvationFree ==
    \A p \in Procs : pc[p] \in {"Hungry1", "Hungry2"} ~> Eating(p)

EatsInfinitelyOften ==
    \A p \in Procs : []<>Eating(p)

THEOREM Spec => [](TypeOK /\ NoNeighborsEat /\ ForkExclusion)
THEOREM Spec => StarvationFree /\ EatsInfinitelyOften

=============================================================================