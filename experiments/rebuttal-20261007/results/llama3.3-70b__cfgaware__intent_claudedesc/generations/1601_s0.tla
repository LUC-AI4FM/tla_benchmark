---------------------------- MODULE FischerMutualExclusion ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, Epsilon, Delta
VARIABLE lock, timers, inCS

Spec == 
  /\ lock = 0
  /\ timers = [i \in 1..N |-> 0]
  /\ inCS = {}
  /\ [][
      /\ \/ \E i \in 1..N : 
          /\ lock = 0
          /\ timers[i] = 0
          /\ lock' = i
          /\ timers' = [timers EXCEPT ![i] = Delta]
          /\ inCS' = inCS
        \/ \E i \in 1..N :
          /\ lock = i
          /\ timers[i] = Delta
          /\ timers' = [timers EXCEPT ![i] = Epsilon]
          /\ lock' = i
          /\ inCS' = inCS \cup {i}
        \/ \A i \in 1..N : timers[i] > 0
        /\ lock' = lock
        /\ timers' = [i \in 1..N |-> timers[i] - 1]
        /\ inCS' = inCS
      /\ UNCHANGED <<lock, timers, inCS>>
    ]

Invariant == 
  /\ lock \in 0 .. N
  /\ \A i \in 1..N : timers[i] \in 0 .. Delta

Liveness == 
  <>[](<> \E i \in 1..N : i \in inCS)

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
=============================================================================