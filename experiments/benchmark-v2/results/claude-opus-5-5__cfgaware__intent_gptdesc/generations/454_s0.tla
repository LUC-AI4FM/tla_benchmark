------------------------- MODULE RealTimeHourHeartbeat -------------------------
EXTENDS Naturals

CONSTANTS Rho, MaxReal, SecondsPerHour

ASSUME /\ Rho \in Nat
       /\ SecondsPerHour \in Nat \ {0}
       /\ MaxReal \in Nat \ {0}
       /\ Rho <= SecondsPerHour
       /\ SecondsPerHour + Rho >= 1

VARIABLES now, timer, hb

vars == <<now, timer, hb>>

RealDom == 0 .. MaxReal

MinTimer == SecondsPerHour - Rho
MaxTimer == SecondsPerHour + Rho

TypeOK ==
  /\ now \in RealDom
  /\ timer \in 0 .. MaxTimer
  /\ hb \in BOOLEAN

Init ==
  /\ now \in RealDom
  /\ timer = 0
  /\ hb = FALSE

Tick ==
  /\ \E d \in 1 .. (MaxReal - now) :
       /\ timer + d <= MaxTimer
       /\ now' = now + d
       /\ timer' = timer + d
  /\ UNCHANGED hb

Heartbeat ==
  /\ timer >= MinTimer
  /\ timer <= MaxTimer
  /\ timer' = 0
  /\ hb' = ~hb
  /\ UNCHANGED now

Next == Tick \/ Heartbeat

Spec == Init /\ [][Next]_vars /\ WF_vars(Tick) /\ WF_vars(Heartbeat)

TimerInv == timer >= 0 /\ timer <= MaxTimer

ClockMonotone == [][now' >= now]_now

NonZeno == \A t \in RealDom : <>(now >= t)

NoPermanentAvoidance ==
  \A t \in RealDom : ([]<>(ENABLED Tick)) => <>(now >= t \/ ~ENABLED Tick)

Property ==
  /\ []TypeOK
  /\ []TimerInv
  /\ ClockMonotone
  /\ NonZeno
  /\ NoPermanentAvoidance
=============================================================================