-------------------------------- MODULE HourClock --------------------------------
(***************************************************************************)
(* A simple discrete hour clock that cycles through hours 1..12 forever.   *)
(***************************************************************************)

EXTENDS Integers, Naturals

CONSTANTS Hours

ASSUME HoursAssumption == Hours = 1..12

VARIABLES hour

(***************************************************************************)
(* Type invariant: hour is always in the set {1, ..., 12}                  *)
(***************************************************************************)
TypeInvariant == hour \in Hours

(***************************************************************************)
(* Helper function to compute the next hour (wrapping 12 -> 1)             *)
(***************************************************************************)
NextHour(h) == IF h = 12 THEN 1 ELSE h + 1

(***************************************************************************)
(* Initial state: the clock starts at some hour in 1..12                   *)
(***************************************************************************)
Init == hour \in Hours

(***************************************************************************)
(* Advance action: move to the next hour                                   *)
(***************************************************************************)
Advance == hour' = NextHour(hour)

(***************************************************************************)
(* Next state relation: the only action is to advance the hour             *)
(***************************************************************************)
Next == Advance

(***************************************************************************)
(* The complete specification with weak fairness to ensure progress        *)
(***************************************************************************)
Spec == Init /\ [][Next]_hour /\ WF_hour(Advance)

(***************************************************************************)
(* SAFETY PROPERTIES                                                       *)
(***************************************************************************)

(* Safety Invariant 1: Hour is always a valid integer in {1,...,12} *)
SafetyInvariant == hour \in Hours

(* Safety Invariant 2: Hour is an integer (implied by above but explicit) *)
HourIsInteger == hour \in Int

(* Combined type and bounds invariant *)
TypeOK == /\ hour \in Hours
          /\ hour \in Int
          /\ hour >= 1
          /\ hour <= 12

(***************************************************************************)
(* LIVENESS PROPERTIES                                                     *)
(***************************************************************************)

(* Liveness 1: Advance steps occur infinitely often *)
(* Expressed as: it's always the case that eventually an advance happens *)
AdvancesInfinitelyOften == []<><<Advance>>_hour

(* Liveness 2: Each hour value appears infinitely often *)
(* For each h in 1..12, eventually the clock shows that hour, always *)
HourAppearsInfinitelyOften(h) == []<>(hour = h)

AllHoursAppearInfinitelyOften == \A h \in Hours : HourAppearsInfinitelyOften(h)

(***************************************************************************)
(* THEOREMS (properties that Spec should satisfy)                          *)
(***************************************************************************)

(* Theorem 1: The specification implies the type invariant always holds *)
THEOREM TypeSafety == Spec => []TypeOK

(* Theorem 2: The specification implies the safety invariant always holds *)
THEOREM Safety == Spec => []SafetyInvariant

(* Theorem 3: Under the specification, advances happen infinitely often *)
THEOREM InfiniteProgress == Spec => AdvancesInfinitelyOften

(* Theorem 4: Under the specification, every hour appears infinitely often *)
THEOREM AllHoursRecur == Spec => AllHoursAppearInfinitelyOften

(***************************************************************************)
(* AUXILIARY LEMMAS                                                        *)
(***************************************************************************)

(* The next hour function preserves the Hours domain *)
LEMMA NextHourPreservesDomain == 
    \A h \in Hours : NextHour(h) \in Hours

(* Advance preserves the type invariant *)
LEMMA AdvancePreservesType == 
    TypeOK /\ Advance => TypeOK'

(* From any hour, we can reach any other hour by repeated advances *)
(* This supports the liveness property that all hours appear infinitely often *)

=============================================================================