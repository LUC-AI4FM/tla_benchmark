--------------------------- MODULE Fischer --------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, Epsilon, Delta

VARIABLE x, timers, cs

Spec == 
  /\ x = 0
  /\ timers = [i \in 1..N |-> 0]
  /\ cs = {}
  /\ [][
      /\ <>(\E i \in 1..N : 
          /\ timers[i] = 0
          /\ x = 0
          /\ x' = i
          /\ timers' = [timers EXCEPT ![i] = Delta]
          /\ UNCHANGED cs)
      /\ <>(\E i \in 1..N : 
          /\ timers[i] = Delta
          /\ x = i
          /\ x' = i
          /\ timers' = [timers EXCEPT ![i] = Epsilon]
          /\ UNCHANGED cs)
      /\ <>(\E i \in 1..N : 
          /\ timers[i] = Epsilon
          /\ x = i
          /\ timers' = [timers EXCEPT ![i] = 0]
          /\ IF x' = i THEN cs' = cs \cup {i} ELSE cs' = cs)
      /\ <>(\E i \in 1..N : 
          /\ timers[i] = 0
          /\ i \in cs
          /\ x' = 0
          /\ cs' = cs \ {i}
          /\ UNCHANGED timers)
      /\ <>(
          /\ \A i \in 1..N : timers[i] > 0
          /\ timers' = [i \in 1..N |-> timers[i] - 1]
          /\ x' = x
          /\ cs' = cs)
      /\ WF(Var _ => 
          /\ <>(\E i \in 1..N : 
              /\ timers[i] = 0
              /\ x = 0
              /\ x' = i
              /\ timers' = [timers EXCEPT ![i] = Delta]
              /\ UNCHANGED cs)
          /\ <>(\E i \in 1..N : 
              /\ timers[i] = Delta
              /\ x = i
              /\ x' = i
              /\ timers' = [timers EXCEPT ![i] = Epsilon]
              /\ UNCHANGED cs)
          /\ <>(\E i \in 1..N : 
              /\ timers[i] = Epsilon
              /\ x = i
              /\ timers' = [timers EXCEPT ![i] = 0]
              /\ IF x' = i THEN cs' = cs \cup {i} ELSE cs' = cs)
          /\ <>(\E i \in 1..N : 
              /\ timers[i] = 0
              /\ i \in cs
              /\ x' = 0
              /\ cs' = cs \ {i}
              /\ UNCHANGED timers))
      ]

Invariant == \A i, j \in 1..N : i # j => ~(i \in cs /\ j \in cs)

Liveness == <>[](~(cs = {}))

THEOREM Spec => []Invariant
THEOREM Spec => Liveness

=============================================================================