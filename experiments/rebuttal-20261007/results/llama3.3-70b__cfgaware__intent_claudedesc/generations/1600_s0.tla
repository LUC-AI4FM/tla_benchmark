---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES flag, trying, critical, last

defaultInitValue == (* Initial values for variables *)
  /\ flag = [i \in 1..N |-> FALSE]
  /\ trying = 0
  /\ critical = 0
  /\ last = 0

Invariant == (* Invariant: at most one process in critical section *)
  /\ critical <= 1
  /\ trying \in 0..N
  /\ last \in 0..N
  /\ flag \in [1..N -> BOOLEAN]

TryAcquire(i) == (* Try to acquire lock for process i *)
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ trying' = i
  /\ UNCHANGED <<critical, last>>

CheckInterference(i) == (* Check if interference occurred for process i *)
  /\ last' = trying
  /\ IF last = i
    THEN critical' = critical + 1
    ELSE critical' = critical

WaitForClear(i) == (* Wait until all other processes clear their flags *)
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<trying, critical, last>>

WaitForZero(i) == (* Wait for second shared variable to become zero *)
  /\ trying' = 0
  /\ UNCHANGED <<flag, critical, last>>

ReleaseLock(i) == (* Release lock after critical section *)
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ trying' = 0
  /\ critical' = 0
  /\ last' = 0

Next(i) == (* Next step for process i *)
  \/ TryAcquire(i)
  \/ (trying = i /\ CheckInterference(i))
  \/ (flag[i] /\ last /= i /\ WaitForClear(i))
  \/ (last = i /\ critical = 0 /\ WaitForZero(i))
  \/ ReleaseLock(i)

Spec == (* Main specification *)
  Init,defaultInitValue
  \* [][Next(1) \/ Next(2) \/ ... \/ Next(N)]_flag,trying,critical,last

Liveness == (* Liveness property: some process enters critical section infinitely often *)
  <>[]<>(critical > 0)

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
=============================================================================