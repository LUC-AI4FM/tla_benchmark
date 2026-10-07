----------------------------- MODULE GCDLoop -----------------------------

EXTENDS Naturals, Integers

VARIABLES u, v, v0, pc

vars == << u, v, v0, pc >>

RECURSIVE GCD(_,_)
GCD(m, n) == IF n = 0 THEN m ELSE GCD(n, m % n)

Init ==
    /\ u = 24
    /\ v \in 1..50
    /\ v0 = v
    /\ pc = "Loop"

Swap ==
    /\ pc = "Loop"
    /\ u < v
    /\ u' = v
    /\ v' = u
    /\ v0' = v0
    /\ pc' = "Loop"

Sub ==
    /\ pc = "Loop"
    /\ u >= v
    /\ u # 0
    /\ u' = u - v
    /\ v' = v
    /\ v0' = v0
    /\ pc' = "Loop"

DoneStep ==
    /\ pc = "Loop"
    /\ u = 0
    /\ u' = u
    /\ v' = v
    /\ v0' = v0
    /\ pc' = "Done"

DoneStutter ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Swap
    \/ Sub
    \/ DoneStep
    \/ DoneStutter

Spec == /\ Init /\ [][Next]_vars

(*
  Safety invariants
*)
TypeInv ==
    /\ u \in Nat
    /\ v \in 1..50
    /\ v0 \in 1..50
    /\ pc \in {"Loop", "Done"}

GCDInvariant ==
    GCD(u, v) = GCD(24, v0)

Correctness ==
    [](pc = "Done" => v = GCD(24, v0))

(*
  Liveness: the loop terminates (eventually reaches Done)
*)
Termination ==
    <>(pc = "Done")

============================================================================