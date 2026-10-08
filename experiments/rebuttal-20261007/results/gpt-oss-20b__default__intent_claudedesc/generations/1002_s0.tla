MODULE Barrier
EXTENDS Naturals, TLC

CONSTANT N

VARIABLE state

Proc == 1..N

(* Type invariant: each process is in one of two states *)
TypeInv == state ∈ [Proc -> {0,1}]

Init == state = [p \in Proc |-> 0]

Arrival(p) ==
    /\ p \in Proc
    /\ state[p] = 0
    /\ state' = [state EXCEPT ![p] = 1]

Reset ==
    /\ state = [p \in Proc |-> 1]
    /\ state' = [p \in Proc |-> 0]

Next == ∃ p \in Proc : Arrival(p) \/ Reset

Spec == Init /\ [] Next

(* Safety invariant: the reset action can only occur when all processes have arrived *)
BarrierProperty == [] (Reset => ∀ p \in Proc : state[p] = 1)

(* Optional liveness property: each process eventually returns to active state *)
Liveness == ∧ ∀ p \in Proc : []<> (state[p] = 0)