```
MODULE TimedMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N, LongDelay, ShortDelay, Infinity

VARIABLES sharedMemory, timers, inCS, tryingToEnter

Init ==
  /\ sharedMemory = 0
  /\ timers = [i \in 1..N |-> Infinity]
  /\ inCS = {}
  /\ tryingToEnter = {}

Next ==
  \/ (\E i \in 1..N :
      /\ tryingToEnter' = tryingToEnter \cup {i}
      /\ sharedMemory' = sharedMemory
      /\ timers' = timers
      /\ inCS' = inCS)
  \/ (\E i \in 1..N :
      /\ tryingToEnter = {i}
      /\ sharedMemory = 0
      /\ sharedMemory' = i
      /\ timers' = [timers EXCEPT ![i] = LongDelay]
      /\ inCS' = inCS)
  \/ (\E i \in 1..N :
      /\ sharedMemory = i
      /\ timers[i] = ShortDelay
      /\ timers' = [timers EXCEPT ![i] = Infinity]
      /\ inCS' = inCS \cup {i}
      /\ tryingToEnter' = tryingToEnter
      /\ sharedMemory' = sharedMemory)
  \/ (\E i \in 1..N :
      /\ inCS = {i}
      /\ sharedMemory' = 0
      /\ timers' = timers
      /\ inCS' = {}
      /\ tryingToEnter' = tryingToEnter)
  \/ (\A i \in 1..N : 
      /\ timers' = [j \in 1..N |-> IF timers[j] # Infinity THEN timers[j] - 1 ELSE timers[j]]
      /\ sharedMemory' = sharedMemory
      /\ inCS' = inCS
      /\ tryingToEnter' = tryingToEnter)

Spec ==
  Init /\ [][Next]_<<sharedMemory, timers, inCS, tryingToEnter>>
  /\ WF_vars(tryingToEnter, i \in 1..N)
  /\ SF_vars(timers, tick)

THEOREM Spec => []MutualExclusion
THEOREM Spec => <>[]TryingToEnterImpliesEntry

MutualExclusion == Cardinality(inCS) <= 1

TryingToEnterImpliesEntry ==
  \A i \in 1..N : tryingToEnter[i] => <>(inCS[i])

tick == /\ \A i \in 1..N : timers' = [j \in 1..N |-> IF timers[j] # Infinity THEN timers[j] - 1 ELSE timers[j]]
          /\ sharedMemory' = sharedMemory
          /\ inCS' = inCS
          /\ tryingToEnter' = tryingToEnter

WF_vars(tryingToEnter, i) == tryingToEnter[i] => <>(~tryingToEnter[i])
SF_vars(timers, tick) == <>tick
```