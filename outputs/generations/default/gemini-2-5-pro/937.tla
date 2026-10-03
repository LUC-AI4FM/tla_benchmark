---- MODULE LiveHourClock ----
EXTENDS Naturals, TemporalLogic

(***************************************************************************)
(* This module specifies a simple 12-hour clock and adds a liveness        *)
(* requirement to ensure it keeps ticking. It is based on the HourClock    *)
(* example from TLA+ resources.                                            *)
(***************************************************************************)

VARIABLES hr

(***************************************************************************)
(* The state constraint. The value of hr should always be an integer       *)
(* from 1 to 12. This is the type invariant.                               *)
(***************************************************************************)
TypeOK == hr \in 1..12

(***************************************************************************)
(* The initial state predicate and the next-state action.                  *)
(***************************************************************************)
Init == hr \in 1..12

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == HCnxt

(***************************************************************************)
(* The safety specification HC asserts that the clock starts correctly and *)
(* that every step is either a valid clock tick (HCnxt) or a stuttering    *)
(* step (where hr is unchanged).                                           *)
(***************************************************************************)
HC == Init /\ [][Next]_hr

(***************************************************************************)
(* The full liveness specification LSpec. It conjoins the safety spec HC   *)
(* with a weak fairness condition on the clock-tick action. The weak       *)
(* fairness WF_hr(Next) asserts that if the clock-tick action Next is      *)
(* continuously enabled, it must eventually be taken. Since Next is        *)
(* always enabled, this ensures the clock does not stop.                   *)
(***************************************************************************)
LSpec == HC /\ WF_hr(Next)

Spec == LSpec

(***************************************************************************)
(* The temporal properties that should hold for any behavior satisfying    *)
(* the LSpec specification.                                                *)
(***************************************************************************)

(* Property 1: The clock ticks infinitely often. *)
TickingHappensInfinitelyOften == []<>Next

(* Property 2: Every possible hour value occurs infinitely often. *)
HourValuesRecurInfinitelyOften == \A h \in 1..12 : []<>(hr = h)

(* Property 3: The type correctness property is an invariant. *)
TypingIsInvariant == []TypeOK

(***************************************************************************)
(* A theorem asserting that the liveness specification implies the desired *)
(* temporal properties. A mechanical proof checker can verify this.        *)
(***************************************************************************)
THEOREM Spec => TickingHappensInfinitelyOften
                  /\ HourValuesRecurInfinitelyOften
                  /\ TypingIsInvariant

(***************************************************************************)
(* A postcondition used in the TLA+ Proof System. It describes the general *)
(* form of a counterexample to a liveness property if the fairness         *)
(* condition were omitted. Specifically, it describes a behavior where the *)
(* clock eventually "settles" or stops ticking, which satisfies the safety *)
(* specification HC but violates liveness.                                 *)
(***************************************************************************)
POSTCONDITION \E c \in 1..12 : <>[](hr = c)

=============================================================================