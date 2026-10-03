---- MODULE DiningPhilosophers ----
EXTENDS Integers, TLC

CONSTANT N
ASSUME N \in Nat /\ N > 1

Philo == 0..N-1
Fork == 0..N-1

VARIABLES pc, sem

vars == <<pc, sem>>

(* The set of states a philosopher's program counter can be in. *)
PCStates == {"Think", "WaitLeft", "WaitRight", "Eat"}

(*
 * The type-correctness invariant.
 * pc[p] is the state of philosopher p.
 * sem[f] = 1 if fork f is available, 0 if taken.
 *)
TypeOK == /\ pc \in [Philo -> PCStates]
          /\ sem \in [Fork -> {0, 1}]

(* Fork definitions: philosopher p sits between Left(p) and Right(p). *)
Left(p) == p
Right(p) == (p + 1) % N

(*
 * Actions for philosophers 1 through N-1.
 * These philosophers pick up their right fork first, then their left fork.
 *)
P_regular(p) ==
    \/ (* Acquire right fork *)
       /\ pc[p] = "Think"
       /\ sem[Right(p)] = 1
       /\ pc' = [pc EXCEPT ![p] = "WaitLeft"]
       /\ sem' = [sem EXCEPT ![Right(p)] = 0]
    \/ (* Acquire left fork *)
       /\ pc[p] = "WaitLeft"
       /\ sem[Left(p)] = 1
       /\ pc' = [pc EXCEPT ![p] = "Eat"]
       /\ sem' = [sem EXCEPT ![Left(p)] = 0]
    \/ (* Release both forks *)
       /\ pc[p] = "Eat"
       /\ pc' = [pc EXCEPT ![p] = "Think"]
       /\ sem' = [sem EXCEPT ![Left(p)] = 1, ![Right(p)] = 1]

(*
 * Actions for philosopher 0.
 * This philosopher picks up forks in the opposite order (left then right)
 * to break symmetry and prevent deadlock.
 *)
P_special_0 ==
    \/ (* Acquire left fork *)
       /\ pc[0] = "Think"
       /\ sem[Left(0)] = 1
       /\ pc' = [pc EXCEPT ![0] = "WaitRight"]
       /\ sem' = [sem EXCEPT ![Left(0)] = 0]
    \/ (* Acquire right fork *)
       /\ pc[0] = "WaitRight"
       /\ sem[Right(0)] = 1
       /\ pc' = [pc EXCEPT ![0] = "Eat"]
       /\ sem' = [sem EXCEPT ![Right(0)] = 0]
    \/ (* Release both forks *)
       /\ pc[0] = "Eat"
       /\ pc' = [pc EXCEPT ![0] = "Think"]
       /\ sem' = [sem EXCEPT ![Left(0)] = 1, ![Right(0)] = 1]

(* The complete set of actions for an arbitrary philosopher p. *)
P(p) == IF p = 0 THEN P_special_0 ELSE P_regular(p)

(*
 * The initial state of the system.
 * All philosophers are thinking, and all forks are available.
 *)
Init == /\ pc = [p \in Philo |-> "Think"]
        /\ sem = [f \in Fork |-> 1]

(*
 * The next-state relation.
 * A step consists of one philosopher taking an action.
 *)
Next == \E p \in Philo : P(p)

(* The complete safety specification. *)
Spec == Init /\ [][Next]_vars

(*
 * The fairness condition.
 * To ensure liveness, we require that each philosopher's process is strongly fair.
 * This means if a philosopher can infinitely often make progress, they must eventually do so.
 *)
Fairness == \A p \in Philo : SF_vars(P(p))

(***************************************************************************)
(*                              PROPERTIES                                 *)
(***************************************************************************)

(* Safety Invariant: No two adjacent philosophers eat at the same time. *)
NoAdjacentEaters ==
    \A p \in Philo : pc[p] = "Eat" => pc[(p + 1) % N] /= "Eat"

(* Liveness Property: Every philosopher eats infinitely often (starvation-freedom). *)
StarvationFreedom ==
    \A p \in Philo : []<>(pc[p] = "Eat")

=============================================================================