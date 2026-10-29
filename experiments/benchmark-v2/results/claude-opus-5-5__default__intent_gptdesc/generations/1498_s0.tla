---------------------------- MODULE TwoActionToggle ----------------------------
EXTENDS Naturals

VARIABLE b

vars == << b >>

(***************************************************************************)
(* Initial condition                                                      *)
(***************************************************************************)
Init == b = FALSE

(***************************************************************************)
(* Two equivalent toggle actions                                          *)
(***************************************************************************)
Toggle1 == b' = ~b

Toggle2 == b' = ~b

(***************************************************************************)
(* Either toggle action may be chosen at any step                         *)
(***************************************************************************)
Next == Toggle1 \/ Toggle2

(***************************************************************************)
(* Fairness: both actions are weakly fair, so neither is starved and      *)
(* toggling continues indefinitely (unbounded time).                       *)
(***************************************************************************)
Fairness == WF_vars(Toggle1) /\ WF_vars(Toggle2)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety properties                                                      *)
(***************************************************************************)

\* The state is always a boolean (no other values are reachable).
TypeOK == b \in BOOLEAN

\* Every reachable state is either FALSE or TRUE.
OnlyBooleanStates == (b = FALSE) \/ (b = TRUE)

\* Each transition really flips the value.
EachStepFlips == [][b' = ~b]_vars

\* Reachable states alternate between FALSE and TRUE.
Alternation == [][ (b = FALSE => b' = TRUE) /\ (b = TRUE => b' = FALSE) ]_vars

\* The system is never stuck: a next action is always available.
NeverStuckInv == ENABLED Next

NeverStuck == [](ENABLED Next)

(***************************************************************************)
(* Liveness properties                                                    *)
(***************************************************************************)

\* Toggling continues forever.
AlwaysEventuallyToggles == []<><<Next>>_vars

\* Both values are visited infinitely often.
InfinitelyOftenTrue  == []<>(b = TRUE)
InfinitelyOftenFalse == []<>(b = FALSE)

\* The system never converges to a fixed point where the value stops changing.
NoFixedPoint == \A v \in BOOLEAN : ~(<>[](b = v))

\* Neither action is permanently ignored.
Toggle1NotStarved == []<><<Toggle1>>_vars
Toggle2NotStarved == []<><<Toggle2>>_vars

(***************************************************************************)
(* Theorems                                                               *)
(***************************************************************************)
THEOREM Spec => []TypeOK
THEOREM Spec => []OnlyBooleanStates
THEOREM Spec => EachStepFlips
THEOREM Spec => Alternation
THEOREM Spec => NeverStuck
THEOREM Spec => AlwaysEventuallyToggles
THEOREM Spec => InfinitelyOftenTrue /\ InfinitelyOftenFalse
THEOREM Spec => NoFixedPoint
THEOREM Spec => Toggle1NotStarved /\ Toggle2NotStarved

=============================================================================