---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

Hours == 0..23

TypeOK == hr \in Hours

HCini == hr \in Hours

HCnxt == hr' = (hr + 1) % 24

HC == HCini /\ [][HCnxt]_hr /\ SF_hr(HCnxt)

---------------------------------------------------------------------------
(* Safety *)
Safety == hr \in Hours

SafetyAlways == []Safety

(* Wrap-around behaviour: every hr-changing step is a correct advance.   *)
(* Stuttering steps (hr' = hr) are permitted by the [ ]_hr form.         *)
WrapAround ==
    [][ /\ (hr = 23 => hr' = 0)
        /\ (hr \in 0..22 => hr' = hr + 1) ]_hr

(* Liveness *)
Progress == \A h \in Hours : []<>(hr = h)

EventualAdvance == []<>(<<HCnxt>>_hr)

---------------------------------------------------------------------------
THEOREM HC => []HCini
THEOREM HC => SafetyAlways
THEOREM HC => WrapAround
THEOREM HC => Progress
THEOREM HC => EventualAdvance
=============================================================================