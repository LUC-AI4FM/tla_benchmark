---------------------------- MODULE MC_LiveHourClock ----------------------------
(***************************************************************************)
(* Type-annotated wrapper for the LiveHourClock specification, intended   *)
(* for use with the Apalache model checker.  The underlying hour clock     *)
(* definitions are inlined here so that this module is self-contained and *)
(* passes SANY without needing a separate LiveHourClock module.  They      *)
(* match the definitions that would be imported with                        *)
(*     INSTANCE LiveHourClock WITH hr <- hr                                 *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

vars == <<hr>>

-----------------------------------------------------------------------------
(* Underlying (Live)HourClock definitions                                   *)
-----------------------------------------------------------------------------

\* Initial condition: the hour is any valid value on a 12-hour clock face.
HCini == hr \in (1 .. 12)

\* Next-state relation: advance the hour cyclically, wrapping 12 -> 1.
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

\* Safety-only hour clock specification.
HC == HCini /\ [][HCnxt]_hr

\* Live hour clock: weak fairness ensures the clock eventually ticks
\* rather than stuttering forever.
LSpec == HC /\ WF_hr(HCnxt)

-----------------------------------------------------------------------------
(* Model-checking configuration entry points                                *)
-----------------------------------------------------------------------------

Init == HCini

Next == HCnxt

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties                                                               *)
-----------------------------------------------------------------------------

\* Type invariant (Apalache-friendly).
TypeOK == hr \in Int

\* The initial condition remains true in every reachable state: the hour
\* always stays within its valid range 1..12.
HCiniInvariant == HCini

\* Liveness: every hour value is reached infinitely often.
AlwaysTicks == \A h \in 1 .. 12 : []<>(hr = h)

\* Liveness: the clock eventually changes value (it never stutters forever).
EventuallyAdvances == \A h \in 1 .. 12 : [](hr = h => <>(hr # h))

THEOREM Spec => []HCiniInvariant
THEOREM Spec => AlwaysTicks
=============================================================================