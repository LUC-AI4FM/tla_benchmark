```
MODULE FischerMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N, Delta, Epsilon
VARIABLES x, timers, cs, pc

Init ==
  /\ x = 0
  /\ timers = [i \in 1..N |-> 0]
  /\ cs = {}
  /\ pc = [i \in 0..N |-> "a"]

Next ==
  \/ \E i \in 1..N : NextProcess(i)
  \/ Tick

Tick ==
  /\ \A i \in 1..N : timers[i] > 0
  /\ timers' = [i \in 1..N |-> timers[i] - 1]
  /\ x' = x
  /\ cs' = cs
  /\ pc' = pc

NextProcess(i) ==
  IF pc[i] = "a"
  THEN
    /\ pc' = [pc EXCEPT ![i] = "b"]
    /\ ELSE
  ELSEIF pc[i] = "b"
  THEN
    /\ x = i
    /\ pc' = [pc EXCEPT ![i] = "c"]
    /\ ELSE
  ELSEIF pc[i] = "c"
  THEN
    /\ x = 0
    /\ timers' = [timers EXCEPT ![i] = Delta]
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "d"]
    /\ ELSE
  ELSEIF pc[i] = "d"
  THEN
    /\ timers[i] = 0
    /\ timers' = [timers EXCEPT ![i] = Epsilon]
    /\ pc' = [pc EXCEPT ![i] = "e"]
    /\ ELSE
  ELSEIF pc[i] = "e"
  THEN
    /\ timers[i] = 0
    /\ x = i
    /\ cs' = cs \cup {i}
    /\ pc' = [pc EXCEPT ![i] = "f"]
    /\ ELSE
  ELSEIF pc[i] = "f"
  THEN
    /\ cs' = cs \ {i}
    /\ x' = 0
    /\ pc' = [pc EXCEPT ![i] = "a"]
    /\ ELSE

Spec ==
  /\ Init
  /\ [][Next]_<<x, timers, cs, pc>>
  /\ WF_vars(NextProcess)(1..N)
  /\ WF_vars(Tick)({0})

Invariant ==
  /\ Delta < Epsilon
  /\ \A i, j \in 1..N : i # j => ~(i \in cs /\ j \in cs)

Liveness ==
  <>[]<>(\E i \in 1..N : i \in cs)

THEOREM Spec => []Invariant
THEOREM Spec => Liveness

Config == 
  /\ N = 3
  /\ Delta = 2
  /\ Epsilon = 3

SomeInCS == <>(\E i \in 1..N : i \in cs)
ClaimLock == <>(x # 0)

Postcondition ==
  /\ [][Next]_<<x, timers, cs, pc>>
  /\ Spec => []Invariant
  /\ Spec => Liveness
  /\ Config => SomeInCS
  /\ Config => ClaimLock

```
Note: The `ELSE` statements in the `NextProcess(i)` action are used to ensure that only one of the possible next states is chosen. The `\A i \in 1..N : timers[i] > 0` condition in the `Tick` action ensures that all timers must be strictly positive before they can be decremented.