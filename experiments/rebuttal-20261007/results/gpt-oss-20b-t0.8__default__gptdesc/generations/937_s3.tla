MODULE HourClockLiveness
EXTENDS HourClock

(* Inherited definitions from HourClock *)
Init   == HourClock.Init
Next   == HourClock.Next

Spec   == Init /\ [][Next]_hr

(* Weak fairness of the hour update action *)
WF_Hr  == WF_Enabled(Next)

(* Augmented specification with liveness requirement *)
LSpec  == Spec /\ WF_Hr

(* Temporal properties *)

TickInfinitely ==
  [] <> Next

RecursAllHours ==
  ∀ h \in {1,2,3,4,5,6,7,8,9,10,11,12} :
    [] <> (hr = h)

TypingInvariant ==
  [] (hr \in 1..12)

(* The specification to be used in proofs *)
Spec   == LSpec

(* Safety invariants derived from the liveness specification *)
THEOREM InvariantThm ==
  ASSUME LSpec
  THEN
    PROVE TickInfinitely /\ RecursAllHours /\ TypingInvariant.

(* Counterexample structure for a settling property *)
THEOREM SettlingCounterexample ==
  (* This counterexample shows that the clock never settles to a single hour value. *)
  ASSUME LSpec
  THEN
    PROVE ~ (<> (hr = 1)).