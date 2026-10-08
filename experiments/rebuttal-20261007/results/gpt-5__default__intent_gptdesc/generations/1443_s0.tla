----------------------------- MODULE CyclicCounter -----------------------------

EXTENDS Naturals

CONSTANTS S
ASSUME S = {0, 1, 2}

VARIABLES x

Succ(s) == IF s = 0 THEN 1 ELSE IF s = 1 THEN 2 ELSE 0

Init == x = 0

Next == x \in S /\ x' = Succ(x)

Spec == Init /\ []Next

(*
 Safety properties
*)
Safety == [] (x \in S)

(*
 Determinism of next-state: from each state, the next state is uniquely determined.
 Expressed as a step property over all steps of any behavior of Spec.
*)
Determinism ==
  [] ( ((x = 0) => x' = 1)
    /\ ((x = 1) => x' = 2)
    /\ ((x = 2) => x' = 0) )

(*
 Reachability: 1 and 2 are each reached within finitely many steps from the initial state.
*)
Reachability == (<>(x = 1)) /\ (<>(x = 2))

(*
 Wrap-around occurrence: the model admits an execution in which a 2→0 step occurs.
 Given Determinism, <> (x = 2) implies such a wrap-around step occurs next.
*)
WrapAroundOnce == <> (x = 2)

(*
 Cycle liveness: every state 0,1,2 is visited infinitely often.
*)
CycleLiveness == []<>(x = 0) /\ []<>(x = 1) /\ []<>(x = 2)

THEOREM Spec => Safety
THEOREM Spec => Determinism
THEOREM Spec => Reachability
THEOREM Spec => WrapAroundOnce
THEOREM Spec => CycleLiveness

=============================================================================