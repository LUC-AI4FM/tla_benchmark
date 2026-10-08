---- MODULE MutexFastSlow ----
EXTENDS Naturals, TLC

CONSTANT N, defaultInitValue

(*
  Process identifiers are 1..N.
  We assume defaultInitValue is a distinguished value not in Proc,
  used here to denote the absence of an owner (None).
*)
Proc == 1..N
None == defaultInitValue

ASSUME N \in Nat \ {0}
ASSUME None \notin Proc

VARIABLES
  intent,   \* [Proc -> BOOLEAN], whether process advertises interest
  owner,    \* in Proc \cup {None}, indicates current owner of the lock (if any)
  inCS,     \* [Proc -> BOOLEAN], whether process is inside the critical section
  pc,       \* [Proc -> {"Idle","FastTry","SlowWait","CS"}], control state
  failed    \* [Proc -> BOOLEAN], whether the last fast attempt was observed to fail

vars == << intent, owner, inCS, pc, failed >>

Init ==
  /\ intent = [i \in Proc |-> FALSE]
  /\ owner  = None
  /\ inCS   = [i \in Proc |-> FALSE]
  /\ pc     = [i \in Proc |-> "Idle"]
  /\ failed = [i \in Proc |-> FALSE]

OthersFalse(i) == \A j \in Proc: j # i => intent[j] = FALSE
CanAcquire(i)  == owner = None /\ OthersFalse(i)

IdleToFast(i) ==
  /\ i \in Proc
  /\ pc[i] = "Idle"
  /\ pc' = [pc EXCEPT ![i] = "FastTry"]
  /\ UNCHANGED << intent, owner, inCS, failed >>

FastSuccess(i) ==
  /\ i \in Proc
  /\ pc[i] = "FastTry"
  /\ CanAcquire(i)
  /\ intent' = [intent EXCEPT ![i] = TRUE]
  /\ owner'  = i
  /\ inCS'   = [inCS EXCEPT ![i] = TRUE]
  /\ pc'     = [pc EXCEPT ![i] = "CS"]
  /\ failed' = [failed EXCEPT ![i] = FALSE]

FastFailToSlow(i) ==
  /\ i \in Proc
  /\ pc[i] = "FastTry"
  /\ ~CanAcquire(i)
  /\ intent' = [intent EXCEPT ![i] = FALSE]
  /\ UNCHANGED owner
  /\ UNCHANGED inCS
  /\ pc'     = [pc EXCEPT ![i] = "SlowWait"]
  /\ failed' = [failed EXCEPT ![i] = TRUE]

\* Slow path: set intent to TRUE when withdrawn
SlowSetIntent(i) ==
  /\ i \in Proc
  /\ pc[i] = "SlowWait"
  /\ intent[i] = FALSE
  /\ intent' = [intent EXCEPT ![i] = TRUE]
  /\ UNCHANGED << owner, inCS, pc, failed >>

\* Withdraw if contention is seen while on slow path
SlowWithdraw(i) ==
  /\ i \in Proc
  /\ pc[i] = "SlowWait"
  /\ intent[i] = TRUE
  /\ ~CanAcquire(i)
  /\ intent' = [intent EXCEPT ![i] = FALSE]
  /\ UNCHANGED << owner, inCS, pc, failed >>

\* Acquire from slow path when window is clear
SlowAcquire(i) ==
  /\ i \in Proc
  /\ pc[i] = "SlowWait"
  /\ intent[i] = TRUE
  /\ CanAcquire(i)
  /\ owner'  = i
  /\ inCS'   = [inCS EXCEPT ![i] = TRUE]
  /\ pc'     = [pc EXCEPT ![i] = "CS"]
  /\ failed' = [failed EXCEPT ![i] = FALSE]
  /\ UNCHANGED intent

\* Optional give-up: leave slow path and retry later
GiveUp(i) ==
  /\ i \in Proc
  /\ pc[i] = "SlowWait"
  /\ intent[i] = FALSE
  /\ pc' = [pc EXCEPT ![i] = "Idle"]
  /\ UNCHANGED << intent, owner, inCS, failed >>

\* Exit the critical section with proper cleanup
ExitCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "CS"
  /\ pc'     = [pc EXCEPT ![i] = "Idle"]
  /\ inCS'   = [inCS EXCEPT ![i] = FALSE]
  /\ intent' = [intent EXCEPT ![i] = FALSE]
  /\ owner'  = None
  /\ failed' = [failed EXCEPT ![i] = FALSE]

Step(i) ==
  IdleToFast(i)
  \/ FastSuccess(i)
  \/ FastFailToSlow(i)
  \/ SlowSetIntent(i)
  \/ SlowWithdraw(i)
  \/ SlowAcquire(i)
  \/ GiveUp(i)
  \/ ExitCS(i)

Next ==
  \E i \in Proc: Step(i)

\* Safety properties (Invariant)
MutualExclusion ==
  \A i, j \in Proc: i # j => ~(inCS[i] /\ inCS[j])

OwnerConsistent ==
  \A i \in Proc: inCS[i] => owner = i /\ intent[i] = TRUE

OwnerReflectsCS ==
  (owner = None) <=> (\A i \in Proc: ~inCS[i])

IdleCleanup ==
  \A i \in Proc: pc[i] = "Idle" => ~inCS[i] /\ intent[i] = FALSE

Invariant ==
  /\ MutualExclusion
  /\ OwnerConsistent
  /\ OwnerReflectsCS
  /\ IdleCleanup

\* Liveness properties
GlobalProgress == [](<> (\E i \in Proc: inCS[i]))
SlowPathProgress == \A i \in Proc: [](pc[i] = "SlowWait" => <> (pc[i] # "SlowWait"))

Liveness == GlobalProgress /\ SlowPathProgress

\* Full specification with fairness assumptions per process
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Proc: WF_vars(Step(i))

====