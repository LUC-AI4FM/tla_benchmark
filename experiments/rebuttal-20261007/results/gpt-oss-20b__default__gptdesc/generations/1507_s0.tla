------------------------------ MODULE TinyClock ------------------------------
EXTENDS Naturals

CONSTANT MaxDepth \in Nat

VARIABLE clock

(* Recursive operator Check *)
Check(b, n) == IF n = 0 THEN FALSE
              ELSE IF b THEN TRUE ELSE Check(~b, n-1)

(* Recursive operator Flip *)
Flip(b, n) == IF n = 0 THEN b
             ELSE Flip(~b, n-1)

(* Type predicate using Check *)
TypePred(b) == Check(b, MaxDepth)

(* Initial state predicate *)
InitState == clock = FALSE /\ TypePred(clock)

(* Constraint-like state predicate *)
ConstraintPred == TypePred(clock)

(* Next-state relation: flip the clock *)
Next == \E newClock : (newClock = Flip(clock, MaxDepth)) /\ newClock /= clock

(* Specification *)
Init == InitState
Spec == Init /\ [][Next]_<<clock>> /\ []TypeInvariant
TypeInvariant == ConstraintPred

(* Comments about TLC coverage behavior for recursive operator call in Init *)
(* In the initial state, the call to Check(clock, MaxDepth) is evaluated. *)

=============================================================================