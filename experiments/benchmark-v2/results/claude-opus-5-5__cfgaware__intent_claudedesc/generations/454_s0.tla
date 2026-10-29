------------------------- MODULE RealTimeHourClock -------------------------
EXTENDS Integers

CONSTANTS Rho, MaxReal, SecondsPerHour

ASSUME /\ Rho \in Nat /\ Rho > 0
       /\ MaxReal \in Nat
       /\ SecondsPerHour \in Nat /\ SecondsPerHour > Rho

VARIABLES hr, now, t

vars == <<hr, now, t>>

(***************************************************************************)
(* Hour-clock component (the "imported" HourClock module, inlined).        *)
(***************************************************************************)
HCini == hr \in 1..12
HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1
HC    == HCini /\ [][HCnxt]_hr

(***************************************************************************)
(* Real-time component. Real is approximated by a finite range.            *)
(***************************************************************************)
Real == 0..MaxReal

TypeOK == /\ now \in Real
          /\ hr \in 1..12
          /\ t \in 0..(SecondsPerHour + Rho)

Init == /\ HCini
        /\ t = 0
        /\ now \in Real

Tick == /\ now' \in {r \in Real : r > now}
        /\ [HCnxt]_hr
        /\ t' = IF hr' # hr THEN 0 ELSE t + (now' - now)
        /\ t + (now' - now) <= SecondsPerHour + Rho
        /\ (hr' # hr) => (t + (now' - now) >= SecondsPerHour - Rho)

\* Time can no longer advance once the bounded range is exhausted.
Halt == /\ now = MaxReal
        /\ UNCHANGED vars

Next == Tick \/ Halt

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Correctness: refinement of HC and the real-time accuracy constraint.    *)
(***************************************************************************)
RTAccuracy ==
    [][ (hr' # hr) =>
          /\ t + (now' - now) >= SecondsPerHour - Rho
          /\ t + (now' - now) <= SecondsPerHour + Rho ]_vars

Property == /\ HC
            /\ RTAccuracy
            /\ [](t <= SecondsPerHour + Rho)

=============================================================================