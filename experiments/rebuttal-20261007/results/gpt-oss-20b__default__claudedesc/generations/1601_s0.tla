MODULE FischerRTME
EXTENDS Naturals

CONSTANTS N = 3, Delta = 2, Epsilon = 3

VARIABLE x, timers, state

Init ==
   /\ x = 0
   /\ timers = [i \in 1..N |-> 0]
   /\ state = [i \in 1..N |-> "idle"]

IdleToSetDelta(i) ==
   /\ state[i] = "idle"
   /\ x = 0
   /\ state' = [state EXCEPT ![i] = "setDelta"]
   /\ timers' = [timers EXCEPT ![i] = Delta]
   /\ x' = i

SetDeltaToWaitTimer(i) ==
   /\ state[i] = "setDelta"
   /\ state' = [state EXCEPT ![i] = "waitTimer"]
   /\ UNCHANGED <<x, timers>>

WaitTimerToCheck(i) ==
   /\ state[i] = "waitTimer"
   /\ timers[i] = 0
   /\ state' = [state EXCEPT ![i] = "check"]
   /\ UNCHANGED <<x, timers>>

CheckToCS(i) ==
   /\ state[i] = "check"
   /\ x = i
   /\ state' = [state EXCEPT ![i] = "cs"]
   /\ UNCHANGED <<x, timers>>

CheckToIdle(i) ==
   /\ state[i] = "check"
   /\ x # i
   /\ state' = [state EXCEPT ![i] = "idle"]
   /\ UNCHANGED <<x, timers>>

CSExit(i) ==
   /\ state[i] = "cs"
   /\ state' = [state EXCEPT ![i] = "idle"]
   /\ x' = 0
   /\ UNCHANGED <<timers>>

Proc(i) ==
   IdleToSetDelta(i) \/ SetDeltaToWaitTimer(i) \/ WaitTimerToCheck(i) \/ CheckToCS(i) \/ CheckToIdle(i) \/ CSExit(i)

Tick ==
   /\ \A i \in 1..N : timers[i] > 0
   /\ timers' = [timers EXCEPT ![i] = timers[i]-1]
   /\ UNCHANGED <<x, state>>

Next ==
   (\E i \in 1..N : Proc(i)) \/ Tick

Spec == Init /\ [][Next]_<<x, state, timers>> /\ (\A i \in 1..N : WF_Proc(i)) /\ WF_Tick

Invariant ==
   \A i,j \in 1..N : i # j => ~(state[i] = "cs" /\ state[j] = "cs")

Liveness ==
   \E i \in 1..N : <>[] (state[i] = "cs")

SomeInCS == \E i \in 1..N : state[i] = "cs"

ClaimLock == Invariant

===============================================================================