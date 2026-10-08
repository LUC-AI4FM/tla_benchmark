---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Integers, TLC

CONSTANT N

VARIABLES flags, owner, inCS, trying

defaultInitValue == 
  (* Initialize all processes as not trying to enter the critical section *)
  [i \in 1..N |-> FALSE]

Spec == 
  /\ flags = [i \in 1..N |-> FALSE]
  /\ owner = 0
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ trying = defaultInitValue

Invariant == 
  (* Mutual exclusion: at most one process is inside the critical section *)
  /\ \A i, j \in 1..N : i # j => ~(inCS[i] /\ inCS[j])
  (* A process can only be in the critical section if it has set its flag and owns the resource *)
  /\ \A i \in 1..N : inCS[i] => (flags[i] /\ owner = i)

TryFast(i) == 
  (* Try to acquire the critical section quickly, but back off if contention is detected *)
  /\ flags' = [flags EXCEPT ![i] = TRUE]
  /\ trying' = [trying EXCEPT ![i] = TRUE]
  /\ IF \E j \in 1..N : j # i /\ flags[j] 
    THEN owner' = owner
    ELSE owner' = i

WithdrawAndWait(i) == 
  (* Withdraw interest and wait for a window where others are not indicating interest *)
  /\ trying' = [trying EXCEPT ![i] = FALSE]
  /\ flags' = [flags EXCEPT ![i] = FALSE]

EnterCS(i) == 
  (* Enter the critical section if successful *)
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ owner' = i

ExitCS(i) == 
  (* Exit the critical section and reset intent and ownership markers *)
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ flags' = [flags EXCEPT ![i] = FALSE]
  /\ owner' = 0
  /\ trying' = [trying EXCEPT ![i] = FALSE]

Next == 
  (* Allow any process to try to enter the critical section *)
  \E i \in 1..N : 
    (trying[i] => TryFast(i)) 
    \/ (~trying[i] /\ flags[i] => EnterCS(i))
    \/ (trying[i] /\ \E j \in 1..N : j # i /\ flags[j] => WithdrawAndWait(i))
    \/ inCS[i] => ExitCS(i)

Liveness == 
  (* No permanent starvation: eventually some process will enter the critical section *)
  <> \E i \in 1..N : inCS[i]
  (* Progress under contention detection: if a process detects contention, it can complete the slower protocol *)
  /\ \A i \in 1..N : trying[i] => <> (inCS[i] \/ trying'[i] = FALSE)
  (* Proper cleanup: on exit, processes reset their advertised intent and any ownership markers *)
  /\ \A i \in 1..N : inCS[i] => <> (flags'[i] = FALSE /\ owner' = 0)

THEOREM Spec => []Invariant
THEOREM Spec => Liveness

=============================================================================