---- MODULE DiningPhilosophers ----
EXTENDS Integers, TLC

CONSTANT N
ASSUME N \in Nat \ {0}

VARIABLES pc, forks

Phils == 0..(N-1)
ForksRange == 0..(N-1)

(* Fork to the left of philosopher i is fork i. *)
Left(i) == i
(* Fork to the right of philosopher i is fork (i-1) mod N. *)
Right(i) == (i - 1 + N) % N

vars == << pc, forks >>

(* Initial state of the system *)
Init ==
    /\ pc = [i \in Phils |-> "Thinking"]
    /\ forks = [f \in ForksRange |-> 1]  (* 1 = available, 0 = taken *)

(* Action for a "normal" philosopher (1 to N-1), who picks up right then left. *)
PNormal(i) ==
    \/ (* Become hungry *)
       /\ pc[i] = "Thinking"
       /\ pc' = [pc EXCEPT ![i] = "Hungry"]
       /\ UNCHANGED forks
    \/ (* Pick up right fork *)
       /\ pc[i] = "Hungry"
       /\ forks[Right(i)] = 1
       /\ pc' = [pc EXCEPT ![i] = "GotRight"]
       /\ forks' = [forks EXCEPT ![Right(i)] = 0]
    \/ (* Pick up left fork *)
       /\ pc[i] = "GotRight"
       /\ forks[Left(i)] = 1
       /\ pc' = [pc EXCEPT ![i] = "Eating"]
       /\ forks' = [forks EXCEPT ![Left(i)] = 0]
    \/ (* Put down both forks *)
       /\ pc[i] = "Eating"
       /\ pc' = [pc EXCEPT ![i] = "Thinking"]
       /\ forks' = [forks EXCEPT ![Right(i)] = 1, ![Left(i)] = 1]

(* Action for the "special" philosopher (0), who picks up left then right. *)
PSpecial(i) ==
    \/ (* Become hungry *)
       /\ pc[i] = "Thinking"
       /\ pc' = [pc EXCEPT ![i] = "Hungry"]
       /\ UNCHANGED forks
    \/ (* Pick up left fork *)
       /\ pc[i] = "Hungry"
       /\ forks[Left(i)] = 1
       /\ pc' = [pc EXCEPT ![i] = "GotLeft"]
       /\ forks' = [forks EXCEPT ![Left(i)] = 0]
    \/ (* Pick up right fork *)
       /\ pc[i] = "GotLeft"
       /\ forks[Right(i)] = 1
       /\ pc' = [pc EXCEPT ![i] = "Eating"]
       /\ forks' = [forks EXCEPT ![Right(i)] = 0]
    \/ (* Put down both forks *)
       /\ pc[i] = "Eating"
       /\ pc' = [pc EXCEPT ![i] = "Thinking"]
       /\ forks' = [forks EXCEPT ![Left(i)] = 1, ![Right(i)] = 1]

(* A single step of a philosopher process *)
Phil(i) ==
    IF i = 0
    THEN PSpecial(i)
    ELSE PNormal(i)

(* The next-state relation *)
Next == \E i \in Phils : Phil(i)

(* Fairness: Strong fairness on each philosopher's process *)
Fairness == \A i \in Phils : SF_vars(Phil(i))

(* The complete specification *)
Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety property: No two adjacent philosophers eat at the same time *)
Invariant == \A i \in Phils : ~(pc[i] = "Eating" /\ pc[(i + 1) % N] = "Eating")

=============================================================================