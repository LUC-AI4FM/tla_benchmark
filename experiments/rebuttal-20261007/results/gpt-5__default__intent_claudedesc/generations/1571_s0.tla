------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N >= 2 /\ N = 4

(*
  Index set of philosophers/forks
*)
P == 0 .. (N - 1)

Right(i) == i
Left(i)  == (i - 1) % N

States == {"Thinking", "Have1", "Eating"}

VARIABLES fork, holdL, holdR, state

vars == << fork, holdL, holdR, state >>

XOR(a, b) == (a \/ b) /\ ~(a /\ b)

(*
  Initialization: all forks free (1), nobody holds any fork, all are thinking
*)
Init ==
  /\ fork  = [j \in P |-> 1]
  /\ holdL = [i \in P |-> FALSE]
  /\ holdR = [i \in P |-> FALSE]
  /\ state = [i \in P |-> "Thinking"]

FirstIdx(i)  == IF i = 0 THEN Left(i) ELSE Right(i)
SecondIdx(i) == IF i = 0 THEN Right(i) ELSE Left(i)

AcquireFirst(i) ==
  /\ i \in P
  /\ state[i] = "Thinking"
  /\ fork[FirstIdx(i)] = 1
  /\ fork' = [fork EXCEPT ![FirstIdx(i)] = 0]
  /\ IF i = 0
        THEN /\ holdL' = [holdL EXCEPT ![i] = TRUE]
             /\ UNCHANGED holdR
        ELSE /\ holdR' = [holdR EXCEPT ![i] = TRUE]
             /\ UNCHANGED holdL
  /\ state' = [state EXCEPT ![i] = "Have1"]

AcquireSecond(i) ==
  /\ i \in P
  /\ state[i] = "Have1"
  /\ (IF i = 0 THEN holdL[i] ELSE holdR[i])
  /\ fork[SecondIdx(i)] = 1
  /\ fork' = [fork EXCEPT ![SecondIdx(i)] = 0]
  /\ IF i = 0
        THEN /\ holdR' = [holdR EXCEPT ![i] = TRUE]
             /\ UNCHANGED holdL
        ELSE /\ holdL' = [holdL EXCEPT ![i] = TRUE]
             /\ UNCHANGED holdR
  /\ state' = [state EXCEPT ![i] = "Eating"]

ReleaseBoth(i) ==
  /\ i \in P
  /\ state[i] = "Eating"
  /\ fork'  = [fork EXCEPT ![Left(i)] = 1, ![Right(i)] = 1]
  /\ holdL' = [holdL EXCEPT ![i] = FALSE]
  /\ holdR' = [holdR EXCEPT ![i] = FALSE]
  /\ state' = [state EXCEPT ![i] = "Thinking"]

PiStep(i) == AcquireFirst(i) \/ AcquireSecond(i) \/ ReleaseBoth(i)

Next == \E i \in P : PiStep(i)

(*
  Fairness: strong fairness for every philosopher's process
*)
Fairness == \A i \in P : SF_vars(PiStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(*
  Safety invariants
*)
TypeInv ==
  /\ fork \in [P -> {0, 1}]
  /\ holdL \in [P -> BOOLEAN]
  /\ holdR \in [P -> BOOLEAN]
  /\ state \in [P -> States]

ForkConsistency ==
  \A j \in P :
    /\ (fork[j] = 1) => /\ ~holdR[j]
                         /\ ~holdL[(j + 1) % N]
    /\ (fork[j] = 0) => XOR(holdR[j], holdL[(j + 1) % N])

EatingHoldsBoth ==
  \A i \in P : (state[i] = "Eating") => (holdL[i] /\ holdR[i])

MutualExclusion ==
  \A i \in P : ~( state[i] = "Eating" /\ state[(i + 1) % N] = "Eating" )

Safety == TypeInv /\ ForkConsistency /\ EatingHoldsBoth /\ MutualExclusion

(*
  Liveness: starvation freedom — each philosopher eats infinitely often
*)
StarvationFreedom ==
  \A i \in P : []<>(state[i] = "Eating")

=============================================================================