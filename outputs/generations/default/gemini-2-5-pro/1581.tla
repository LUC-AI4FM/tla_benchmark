---- MODULE DiningPhilosophers ----
EXTENDS Integers

CONSTANT N
ASSUME N \in Nat /\ N > 1

Philosophers == 0..(N-1)
Forks == 0..(N-1)

(*
Philosopher `p` sits between fork `Left(p)` and `Right(p)`.
- Fork `p` is to philosopher `p`'s left.
- Fork `(p-1+N)%N` is to philosopher `p`'s right.
- Fork `p` is shared by philosopher `p` and philosopher `(p+1)%N`.
*)
Left(p) == p
Right(p) == (p - 1 + N) % N

(*
Asymmetric fork acquisition strategy:
- Philosophers 1..N-1 pick up their right fork, then their left.
- Philosopher 0 picks up their left fork, then their right.
*)
FirstFork(p) == IF p = 0 THEN Left(p) ELSE Right(p)
SecondFork(p) == IF p = 0 THEN Right(p) ELSE Left(p)

VARIABLES pc, sem

vars == <<pc, sem>>

TypeOK ==
    /\ pc \in [Philosophers -> {"think", "hungry", "got_first", "eat"}]
    /\ sem \in [Forks -> {0, 1}]  \* 1 is available, 0 is taken

Init ==
    /\ pc = [p \in Philosophers |-> "think"]
    /\ sem = [f \in Forks |-> 1]

(* Actions for philosopher p *)

BecomeHungry(p) ==
    /\ pc[p] = "think"
    /\ pc' = [pc EXCEPT ![p] = "hungry"]
    /\ UNCHANGED sem

PickupFirstFork(p) ==
    /\ pc[p] = "hungry"
    /\ sem[FirstFork(p)] = 1
    /\ pc' = [pc EXCEPT ![p] = "got_first"]
    /\ sem' = [sem EXCEPT ![FirstFork(p)] = 0]

PickupSecondFork(p) ==
    /\ pc[p] = "got_first"
    /\ sem[SecondFork(p)] = 1
    /\ pc' = [pc EXCEPT ![p] = "eat"]
    /\ sem' = [sem EXCEPT ![SecondFork(p)] = 0]

PutDownForks(p) ==
    /\ pc[p] = "eat"
    /\ pc' = [pc EXCEPT ![p] = "think"]
    /\ sem' = [sem EXCEPT ![Left(p)] = 1, ![Right(p)] = 1]

(* A philosopher's complete set of possible actions *)
Phil(p) ==
    \/ BecomeHungry(p)
    \/ PickupFirstFork(p)
    \/ PickupSecondFork(p)
    \/ PutDownForks(p)

(* The global next-state relation *)
Next == \E p \in Philosophers : Phil(p)

(* Fairness condition: Strong Fairness for each philosopher's process *)
Fairness == \A p \in Philosophers : SF_vars(Phil(p))

(* The full temporal specification *)
Spec == Init /\ [][Next]_vars /\ Fairness

\*
\* PROPERTIES
\*

(* Safety: Adjacent philosophers do not eat simultaneously. *)
MutualExclusion ==
    \A p \in Philosophers :
        pc[p] = "eat" => pc[(p + 1) % N] /= "eat"

(* Liveness: Every philosopher eventually eats, infinitely often. *)
StarvationFreedom ==
    \A p \in Philosophers : []<>(pc[p] = "eat")

=============================================================================