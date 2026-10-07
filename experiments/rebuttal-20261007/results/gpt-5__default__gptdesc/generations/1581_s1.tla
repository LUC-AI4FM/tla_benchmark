------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
  Philosophers are 0..N-1 arranged in a ring.
  Fork i is between philosopher i and (i+1) mod N.
  Philosopher 0 picks up Left then Right; others pick up Right then Left.
*)

Proc == 0..(N-1)
Fork == Proc

Succ(p) == IF p = N-1 THEN 0 ELSE p + 1
Pred(p) == IF p = 0 THEN N - 1 ELSE p - 1

Left(p)  == Pred(p)
Right(p) == p

FirstFork(p)  == IF p = 0 THEN Left(p) ELSE Right(p)
SecondFork(p) == IF p = 0 THEN Right(p) ELSE Left(p)

Labels == {"think", "take1", "take2", "eat", "put1", "put2"}

OwnerSet == Proc \cup {"free"}

VARIABLES pc, sem

vars == << pc, sem >>

TypeOK ==
  /\ pc \in [Proc -> Labels]
  /\ sem \in [Fork -> OwnerSet]

Init ==
  /\ pc  = [p \in Proc |-> "think"]
  /\ sem = [f \in Fork |-> "free"]

ThinkToTake1(p) ==
  /\ p \in Proc
  /\ pc[p] = "think"
  /\ pc' = [pc EXCEPT ![p] = "take1"]
  /\ UNCHANGED sem

Take1(p) ==
  /\ p \in Proc
  /\ pc[p] = "take1"
  /\ sem[FirstFork(p)] = "free"
  /\ pc'  = [pc  EXCEPT ![p] = "take2"]
  /\ sem' = [sem EXCEPT ![FirstFork(p)] = p]

Take2(p) ==
  /\ p \in Proc
  /\ pc[p] = "take2"
  /\ sem[SecondFork(p)] = "free"
  /\ pc'  = [pc  EXCEPT ![p] = "eat"]
  /\ sem' = [sem EXCEPT ![SecondFork(p)] = p]

EatToPut1(p) ==
  /\ p \in Proc
  /\ pc[p] = "eat"
  /\ pc' = [pc EXCEPT ![p] = "put1"]
  /\ UNCHANGED sem

Put1(p) ==
  /\ p \in Proc
  /\ pc[p] = "put1"
  /\ sem[SecondFork(p)] = p
  /\ pc'  = [pc  EXCEPT ![p] = "put2"]
  /\ sem' = [sem EXCEPT ![SecondFork(p)] = "free"]

Put2(p) ==
  /\ p \in Proc
  /\ pc[p] = "put2"
  /\ sem[FirstFork(p)] = p
  /\ pc'  = [pc  EXCEPT ![p] = "think"]
  /\ sem' = [sem EXCEPT ![FirstFork(p)] = "free"]

Phil(p) ==
  ThinkToTake1(p) \/ Take1(p) \/ Take2(p) \/ EatToPut1(p) \/ Put1(p) \/ Put2(p)

Next ==
  \E p \in Proc : Phil(p)

Spec ==
  Init /\ [][Next]_vars /\ (\A p \in Proc : SF_vars(Phil(p)))

(*
  Safety: Adjacent philosophers never eat simultaneously.
*)
NoAdjacentEat ==
  \A p \in Proc :
    ~(pc[p] = "eat" /\ pc[Succ(p)] = "eat")

(*
  Liveness: Starvation-freedom — each philosopher eats infinitely often.
*)
StarvationFree ==
  \A p \in Proc : []<>(pc[p] = "eat")

==============================