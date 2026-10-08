---- MODULE Counter ----
EXTENDS Naturals

VARIABLE c

(*
  A single integer counter that starts at 1, increments by 1 until it reaches 5,
  and then remains at 5 forever.
*)

Init ==
  c = 1

Inc ==
  /\ c < 5
  /\ c' = c + 1

Stay ==
  /\ c = 5
  /\ c' = c

Next ==
  Inc \/ Stay

(*
  Spec includes:
  - Initialization at 1
  - Safety via the step relation Next
  - Weak fairness of Inc: if Inc stays enabled continuously, it must eventually occur
*)
Spec ==
  /\ Init
  /\ [][Next]_<<c>>
  /\ WF_<<c>>(Inc)

(*
  Auxiliary invariants and safety properties:
  - Bounds: counter stays within 1..5
  - Monotonicity: counter is nondecreasing
  - Step safety: when below 5 it increments by exactly 1; at 5 it stays
*)
Bounds ==
  [] (c \in 1..5)

Monotonic ==
  [] (c' >= c)

Safety ==
  [] ( (c < 5 => c' = c + 1) /\ (c = 5 => c' = c) )

(*
  Liveness: eventual stabilization at 5
*)
Liveness ==
  <>[] (c = 5)

====