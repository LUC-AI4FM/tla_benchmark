---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLES inFastDoorway, intentFlags, inCriticalSection

inFastDoorway == <<>>
intentFlags == [i \in 1..N |-> FALSE]
inCriticalSection == [i \in 1..N |-> FALSE]

TryEnter(i) ==
  /\ ~inFastDoorway
  /\ intentFlags[i] = FALSE
  /\ inFastDoorway' = {i}
  /\ intentFlags' = [intentFlags EXCEPT ![i] = TRUE]
  /\ UNCHANGED inCriticalSection

WithdrawAndWait(i) ==
  /\ inFastDoorway = {i}
  /\ intentFlags[i] = TRUE
  /\ inFastDoorway' = {}
  /\ intentFlags' = [intentFlags EXCEPT ![i] = TRUE]
  /\ UNCHANGED inCriticalSection

EnterCriticalSection(i) ==
  /\ ~inFastDoorway
  /\ intentFlags[i] = TRUE
  /\ \A j \in 1..N : j < i => intentFlags[j] = FALSE
  /\ inCriticalSection' = [inCriticalSection EXCEPT ![i] = TRUE]
  /\ UNCHANGED inFastDoorway
  /\ UNCHANGED intentFlags

ExitCriticalSection(i) ==
  /\ inCriticalSection[i]
  /\ inCriticalSection' = [inCriticalSection EXCEPT ![i] = FALSE]
  /\ intentFlags' = [intentFlags EXCEPT ![i] = FALSE]
  /\ UNCHanged inFastDoorway

Next ==
  \E i \in 1..N :
    \/ TryEnter(i)
    \/ WithdrawAndWait(i)
    \/ EnterCriticalSection(i)
    \/ ExitCriticalSection(i)

Spec == Init /\ [][Next]_<<inFastDoorway, intentFlags, inCriticalSection>>

Invariant == 
  /\ ~inFastDoorway \subseteq {i \in 1..N : intentFlags[i]}
  /\ \A i \in 1..N : inCriticalSection[i] => intentFlags[i]
  /\ Cardinality(inCriticalSection) <= 1

Liveness == \A i \in 1..N : <>inCriticalSection[i]

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
=============================================================================