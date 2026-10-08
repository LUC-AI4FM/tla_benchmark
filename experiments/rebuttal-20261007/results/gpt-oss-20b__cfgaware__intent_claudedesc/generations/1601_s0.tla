------------------------------ MODULE FischerMutualExclusion ------------------------------
EXTENDS Naturals

CONSTANTS N, Epsilon, Delta

VARIABLES lock, timers, state

(* Types *)
StateSet == {"Idle", "SetDelta", "ResetEpsilon", "InCS"}

Init ==
  /\ lock = 0
  /\ timers = [i \in 1..N |-> 0]
  /\ state = [i \in 1..N |-> "Idle"]

(* Process actions *)
TryEnter(i) ==
  /\ i \in 1..N
  /\ state[i] = "Idle"
  /\ lock = 0
  /\ lock' = i
  /\ timers' = [timers EXCEPT ![i] = Delta]
  /\ state' = [state EXCEPT ![i] = "SetDelta"]

ResetEpsilon(i) ==
  /\ i \in 1..N
  /\ state[i] = "SetDelta"
  /\ timers' = [timers EXCEPT ![i] = Epsilon]
  /\ state' = [state EXCEPT ![i] = "ResetEpsilon"]

CheckLock(i) ==
  /\ i \in 1..N
  /\ state[i] = "ResetEpsilon"
  /\ timers[i] = 0
  /\ lock = i
  /\ state' = [state EXCEPT ![i] = "InCS"]

Abort(i) ==
  /\ i \in 1..N
  /\ state[i] = "ResetEpsilon"
  /\ timers[i] = 0
  /\ lock #= i
  /\ state' = [state EXCEPT ![i] = "Idle"]

ExitCS(i) ==
  /\ i \in 1..N
  /\ state[i] = "InCS"
  /\ lock' = 0
  /\ state' = [state EXCEPT ![i] = "Idle"]

ClockTick ==
  /\ \A i \in 1..N : timers[i] > 0
  /\ timers' = [i \in 1..N |-> timers[i] - 1]

Next ==
  \E i \in 1..N :
    (TryEnter(i) \/ ResetEpsilon(i) \/ CheckLock(i) \/ Abort(i) \/ ExitCS(i))
  \/ ClockTick

Spec == Init /\ [][Next]_<<lock, timers, state>>

Invariant ==
  \A i,j \in 1..N : (i # j) => ~(state[i] = "InCS" /\ state[j] = "InCS")

Liveness ==
  \E i \in 1..N : []<> (state[i] = "InCS")
=============================================================================