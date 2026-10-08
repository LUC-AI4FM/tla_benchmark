------------------------------ MODULE FischerTimed ------------------------------
EXTENDS Naturals, TLC

CONSTANTS N, Delta, Epsilon, Infinity
ASSUME N > 0 /\ Delta >= 0 /\ Epsilon > 0

VARIABLES x, want, timers

(* Helper predicate *)
InCS(i) == (x = i)

Init ==
   /\ x = 0
   /\ want = [i \in 1..N |-> FALSE]
   /\ timers = [i \in 1..N |-> Infinity]

Request(i) ==
   /\ NOT want[i]
   /\ x' = x
   /\ want' == [j \in 1..N |-> IF j = i THEN TRUE ELSE want[j]]
   /\ timers' == [j \in 1..N |-> IF j = i THEN Delta ELSE timers[j]]

TryAcquire(i) ==
   /\ want[i]
   /\ timers[i] > 0
   /\ x = 0
   /\ x' = i
   /\ want' = want
   /\ timers' = timers

ExitCS(i) ==
   /\ InCS(i)
   /\ x' = 0
   /\ want' == [j \in 1..N |-> IF j = i THEN FALSE ELSE want[j]]
   /\ timers' == [j \in 1..N |-> IF j = i THEN Infinity ELSE timers[j]]

Abort(i) ==
   /\ want[i]
   /\ timers[i] = 0
   /\ x /= i
   /\ want' == [j \in 1..N |-> IF j = i THEN FALSE ELSE want[j]]
   /\ timers' == [j \in 1..N |-> IF j = i THEN Infinity ELSE timers[j]]

Tick ==
   LET newTimers == [j \in 1..N |
                     IF timers[j] = Infinity THEN Infinity
                        ELSE IF timers[j] <= Epsilon THEN 0
                        ELSE timers[j] - Epsilon]
   IN
     /\ x' = x
     /\ want' = want
     /\ timers' = newTimers

Next ==
   \/ Tick
   \/ \E i \in 1..N : Request(i)
   \/ \E i \in 1..N : TryAcquire(i)
   \/ \E i \in 1..N : ExitCS(i)
   \/ \E i \in 1..N : Abort(i)

Spec == Init /\ [][Next]_<<x, want, timers>>

(* Safety invariant: mutual exclusion *)
MutualExclusion ==
   \A i,j \in 1..N : (i # j) => ~(InCS(i) /\ InCS(j))

THEOREM Safety == Spec => [] MutualExclusion

(* Liveness property: some process is infinitely often in CS *)
LTLSpec == InfinitelyOften[\E i \in 1..N : InCS(i)]

LTLSPEC LTLSpec
=============================================================================