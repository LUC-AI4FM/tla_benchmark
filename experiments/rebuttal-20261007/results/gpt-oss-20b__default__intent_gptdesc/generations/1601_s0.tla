MODULE Fischer
EXTENDS Naturals, TLC

CONSTANTS N, LongDelay, ShortDelay, INF

ASSUME
  LongDelay >= ShortDelay
  INF > LongDelay

ProcSet == 1..N

VARIABLE mem, timers, cs

vars == <<mem, timers, cs>>

Init ==
  /\ mem = 0
  /\ timers = [i \in ProcSet |-> INF]
  /\ cs = {}

Tick ==
  /\ timers' = [j \in ProcSet |-> IF timers[j] > 0 THEN timers[j]-1 ELSE timers[j]]
  /\ UNCHANGED <<mem, cs>>

TryEnter(i) ==
  /\ i \in ProcSet
  /\ mem = 0
  /\ timers[i] = INF
  /\ mem' = i
  /\ timers' = [j \in ProcSet |-> IF j = i THEN ShortDelay ELSE timers[j]]
  /\ UNCHANGED <<cs>>

EnterCS(i) ==
  /\ i \in ProcSet
  /\ mem = i
  /\ timers[i] = 0
  /\ cs' = {i}
  /\ UNCHANGED <<mem, timers>>

Exit(i) ==
  /\ i \in ProcSet
  /\ i \in cs
  /\ cs' = {}
  /\ mem' = 0
  /\ timers' = [j \in ProcSet |-> IF j = i THEN INF ELSE timers[j]]

Next == \/ Tick
        \/ \E i \in ProcSet : TryEnter(i)
        \/ \E i \in ProcSet : EnterCS(i)
        \/ \E i \in ProcSet : Exit(i)

Spec == Init /\ [][Next]_vars /\
        \A i \in ProcSet : Fairness(TryEnter(i) \/ EnterCS(i)) /\ Fairness(Tick)

MutualExclusion ==
  \A i,j \in ProcSet : i # j => ~(i \in cs /\ j \in cs)

Safety == [] MutualExclusion

Liveness ==
  \A i \in ProcSet : <> (i \in cs)

PotentialViolation ==
  \E i,j \in ProcSet : i # j /\ i \in cs /\ j \in cs

END MODULE