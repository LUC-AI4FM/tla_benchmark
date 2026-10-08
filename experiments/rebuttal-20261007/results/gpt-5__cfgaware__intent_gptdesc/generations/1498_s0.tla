------------------------------- MODULE Toggle -------------------------------

(*
  Simple two-action toggle system:
  - Single boolean state variable x
  - Initially x = FALSE
  - Two actions ToggleA and ToggleB; each flips x
  - Next is the disjunction of the two toggle actions
  - Fairness prevents either action from being starved
*)

VARIABLE x

Init == x = FALSE

ToggleA == x' = ~x
ToggleB == x' = ~x

Next == ToggleA \/ ToggleB

Spec == Init /\ [][Next]_x /\ WF_x(ToggleA) /\ WF_x(ToggleB)

(*
  Safety properties to check (state and step well-formedness):
*)
TypeOK == [] (x \in BOOLEAN)

(*
  Liveness: the system never gets stuck; from any state an action is enabled.
*)
NotStuck == []<>(ENABLED Next)

(*
  Fairness requirement: neither ToggleA nor ToggleB can be ignored forever.
*)
Fair == WF_x(ToggleA) /\ WF_x(ToggleB)

(*
  Correctness properties to check:

  - Reachable states alternate between FALSE and TRUE in the sense that
    from any point, the opposite value recurs in the future.
  - The system does not converge to a fixed point: both TRUE and FALSE
    occur infinitely often.
*)
Alternation ==
  [] ((x = TRUE) => <> (x = FALSE))
  /\ [] ((x = FALSE) => <> (x = TRUE))

NoFixedPoint ==
  [] (<> (x = TRUE)) /\ [] (<> (x = FALSE))

=============================================================================