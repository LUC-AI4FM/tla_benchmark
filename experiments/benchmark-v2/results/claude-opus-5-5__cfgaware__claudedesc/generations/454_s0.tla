---------------------------- MODULE test63 ----------------------------
(***************************************************************************)
(* Test of the fix (11 March 2009) concerning the use of [A]_v inside a    *)
(* next-state relation.  The hour-clock definitions of the companion       *)
(* module test63a are included inline so the module stands alone.          *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Rho, MaxReal, SecondsPerHour

VARIABLES hr, now, t

-----------------------------------------------------------------------------
(* Hour clock (as in test63a) *)
HCini == hr \in 1..12

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------
Real == 0..MaxReal

vars == <<hr, now, t>>

TypeOK == /\ now \in Nat
          /\ hr \in 1..12

NowNext == now' \in {r \in Real : r > now}

TNext == t' = IF HCnxt THEN 0 ELSE t + (now' - now)

MaxTime == t' <= SecondsPerHour + Rho

MinTime == HCnxt => t >= SecondsPerHour - Rho

BigInit == /\ HCini
           /\ t = 0
           /\ now \in Real

BigNext == /\ [NowNext]_now
           /\ [HCnxt]_hr
           /\ TNext
           /\ MaxTime
           /\ MinTime

Spec == BigInit /\ [][BigNext]_vars

-----------------------------------------------------------------------------
NonZeno == \A r \in Real : <>(now >= r)

ErrorTemporal == <>[](hr = 12)

RT == /\ now \in Real
      /\ [][NowNext]_now

HCTime == /\ t = 0
          /\ [][/\ TNext
                /\ MaxTime
                /\ MinTime]_<<t, hr, now>>

Property == HC

=============================================================================