---- MODULE DiningPhilosophers ----
EXTENDS Integers, TLC

CONSTANT N

ASSUME N \in 1..MaxInt

VARIABLES pc, sem

Philosophers == 0..(N-1)
Forks == 0..(N-1)

(* The fork to the left of philosopher i *)
Left(i) == i

(* The fork to the right of philosopher i *)
Right(i) == (i + 1) % N

(* The first fork philosopher i tries to pick up, per the asymmetric strategy.
 * Philosopher 0 picks up Left then Right. Others pick up Right then Left. *)
FirstFork(i) == IF i = 0 THEN Left(i) ELSE Right(i)

(* The second fork philosopher i tries to pick up *)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

vars == <<pc, sem>>

(* Initially, all philosophers are thinking and all forks are available.
 * The control-flow variable pc can be in one of four states:
 * "thinking", "hungry", "got_first" (has acquired the first fork), or "eating". *)
Init ==
    /\ pc = [i \in Philosophers |-> "thinking"]
    /\ sem = [f \in Forks |-> 1]

(* A philosopher in state "thinking" can become "hungry". *)
StartEating(i) ==
    /\ pc[i] = "thinking"
    /\ pc' = [pc EXCEPT ![i] = "hungry"]
    /\ UNCHANGED sem

(* A "hungry" philosopher picks up their first designated fork, if available. *)
PickupFirstFork(i) ==
    /\ pc[i] = "hungry"
    /\ sem[FirstFork(i)] = 1
    /\ pc' = [pc EXCEPT ![i] = "got_first"]
    /\ sem' = [sem EXCEPT ![FirstFork(i)] = 0]

(* A philosopher holding one fork ("got_first") picks up their second, if available. *)
PickupSecondFork(i) ==
    /\ pc[i] = "got_first"
    /\ sem[SecondFork(i)] = 1
    /\ pc' = [pc EXCEPT ![i] = "eating"]
    /\ sem' = [sem EXCEPT ![SecondFork(i)] = 0]

(* An "eating" philosopher puts down both forks and returns to "thinking". *)
PutdownForks(i) ==
    /\ pc[i] = "eating"
    /\ pc' = [pc EXCEPT ![i] = "thinking"]
    /\ sem' = [sem EXCEPT ![Left(i)] = 1, ![Right(i)] = 1]

(* The possible actions for a single philosopher process. *)
P(i) ==
    \/ StartEating(i)
    \/ PickupFirstFork(i)
    \/ PickupSecondFork(i)
    \/ PutdownForks(i)

(* The global next-state relation is the disjunction of all possible process actions. *)
Next == \E i \in Philosophers : P(i)

(* The full specification: starts in Init, always takes Next steps,
 * and is strongly fair to each philosopher's process. *)
Spec == Init /\ [][Next]_vars /\ \A i \in Philosophers : SF_vars(P(i))

(* Safety Invariant: Adjacent philosophers do not eat simultaneously. *)
Invariant == \A i \in Philosophers :
    (pc[i] = "eating") => (pc[(i + 1) % N] /= "eating")

(* Liveness Property: Every philosopher gets to eat infinitely often. *)
StarvationFree == \A i \in Philosophers : []<>(pc[i] = "eating")

=============================================================================