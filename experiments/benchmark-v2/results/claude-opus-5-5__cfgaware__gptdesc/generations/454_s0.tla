---------------------------- MODULE RealTimeHourClock ----------------------------
(***************************************************************************)
(* A real-time hour clock.  The real-valued variable "now" advances        *)
(* monotonically.  The hour variable hr ticks according to the hour clock  *)
(* operators.  The timer t accumulates elapsed time, and is reset to 0     *)
(* whenever the clock ticks (HCnxt).  For model checking, "real" time is   *)
(* modelled by the naturals bounded by MaxReal.                            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Rho,             \* allowed timing jitter
          MaxReal,         \* bound on time, for finite model checking
          SecondsPerHour   \* nominal length of an hour

ASSUME /\ Rho \in Nat
       /\ MaxReal \in Nat
       /\ SecondsPerHour \in Nat
       /\ Rho <= SecondsPerHour

VARIABLES now, hr, t

vars == <<now, hr, t>>

Real == 0..MaxReal

-----------------------------------------------------------------------------
(***************************************************************************)
(* The hour clock (the operators an instantiated HourClock would provide). *)
(***************************************************************************)
HCini == hr \in 1..12

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------
(***************************************************************************)
(* Real time.                                                              *)
(***************************************************************************)
NowNext(v) == /\ now' \in {r \in Real : r > now}
              /\ UNCHANGED v

RT(v) == /\ now \in Real
         /\ [][NowNext(v)]_now

RTnow == RT(<<hr, t>>)

-----------------------------------------------------------------------------
(***************************************************************************)
(* The timer.  A subscripted action <<HCnxt>>_hr is used inside the        *)
(* next-state relation TNext.                                              *)
(***************************************************************************)
TNext == t' = IF <<HCnxt>>_hr THEN 0 ELSE t + (now' - now)

Timer == (t = 0) /\ [][TNext]_<<t, hr, now>>

IsTimer(x) == /\ x = 0
              /\ [][x' = IF <<HCnxt>>_hr THEN 0 ELSE x + (now' - now)]_<<x, hr, now>>

(* A subscripted action used inside an action formula. *)
BigNext == /\ [HCnxt]_hr
           /\ [TNext]_t

MaxTime == [](t \leq SecondsPerHour + Rho)

MinTime == [][HCnxt => t \geq SecondsPerHour - Rho]_hr

(* The timing constraints on the hour clock, with t left visible so that   *)
(* the formula can be model checked (instead of hiding t with \EE).        *)
HCTime == Timer /\ MaxTime /\ MinTime

-----------------------------------------------------------------------------
(***************************************************************************)
(* An explicit initial predicate / next-state relation for model checking *)
(* that implements HC /\ RTnow /\ HCTime.                                  *)
(***************************************************************************)
TypeOK == /\ now \in Real
          /\ hr \in 1..12
          /\ t \in 0..(SecondsPerHour + Rho)

Init == /\ now \in Real
        /\ HCini
        /\ t = 0

Tick == /\ t \geq SecondsPerHour - Rho
        /\ HCnxt
        /\ t' = 0
        /\ UNCHANGED now

Advance == /\ now < MaxReal
           /\ \E d \in 1..(MaxReal - now) :
                 /\ t + d \leq SecondsPerHour + Rho
                 /\ now' = now + d
                 /\ t' = t + d
           /\ UNCHANGED hr

(* Time is exhausted in the finite model: allow stuttering to avoid deadlock. *)
Done == /\ now = MaxReal
        /\ UNCHANGED vars

Next == Tick \/ Advance \/ Done

Fairness == WF_vars(Tick) /\ WF_vars(Advance)

Spec == Init /\ [][Next]_vars /\ Fairness

FullSpec == HC /\ RTnow /\ HCTime

-----------------------------------------------------------------------------
(***************************************************************************)
(* Progress properties.                                                    *)
(***************************************************************************)
NZ(v) == \A r \in Real : WF_v(NowNext(v)) => <>(now \geq r)

NonZeno == \A r \in Real : <>(now \geq r)

ClockKeepsTicking == []<><<HCnxt>>_hr

(* An explicit temporal formula about now remaining different from 4. *)
ErrorTemporal == <>[](now # 4)

Property == ErrorTemporal

=============================================================================