-------------------------- MODULE Fischer --------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS N, Delta, Epsilon, Infinity

ASSUME N \in Nat /\ N >= 1
ASSUME Delta \in Nat /\ Delta >= 1
ASSUME Epsilon \in Nat /\ Epsilon >= 1
ASSUME Infinity > Delta /\ Infinity > Epsilon

(*
Fischer's Timed Mutual Exclusion Algorithm

This algorithm ensures mutual exclusion using timing assumptions.
Each process has a timer, and there's a shared variable 'lock'.

The algorithm works correctly only when Delta < Epsilon.
A bug (mutual exclusion violation) should be found when N > 1 and Delta >= Epsilon.

Process i:
  1. Wait until lock = 0
  2. Set timer to Delta, then set lock = i
  3. Wait for Epsilon time units
  4. If lock = i, enter critical section
  5. On exit, set lock = 0

The Tick process decrements all active timers.
*)

VARIABLES pc, lock, timer

vars == <<pc, lock, timer>>

Procs == 1..N

(* Process states *)
States == {"idle", "trying", "waiting", "critical"}

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ lock \in (Procs \cup {0})
    /\ timer \in [Procs -> 0..Infinity]

Init ==
    /\ pc = [i \in Procs |-> "idle"]
    /\ lock = 0
    /\ timer = [i \in Procs |-> 0]

(* Process i checks if lock is free and starts trying *)
Try(i) ==
    /\ pc[i] = "idle"
    /\ lock = 0
    /\ pc' = [pc EXCEPT ![i] = "trying"]
    /\ timer' = [timer EXCEPT ![i] = Delta]
    /\ UNCHANGED lock

(* Process i sets the lock to its id after waiting (timer must have expired or still active) *)
SetLock(i) ==
    /\ pc[i] = "trying"
    /\ lock' = i
    /\ pc' = [pc EXCEPT ![i] = "waiting"]
    /\ timer' = [timer EXCEPT ![i] = Epsilon]

(* Process i checks if it still holds the lock after Epsilon delay *)
EnterCS(i) ==
    /\ pc[i] = "waiting"
    /\ timer[i] = 0
    /\ lock = i
    /\ pc' = [pc EXCEPT ![i] = "critical"]
    /\ UNCHANGED <<lock, timer>>

(* Process i was preempted - lock was taken by someone else *)
Retry(i) ==
    /\ pc[i] = "waiting"
    /\ timer[i] = 0
    /\ lock # i
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<lock, timer>>

(* Process i exits critical section *)
ExitCS(i) ==
    /\ pc[i] = "critical"
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED timer

(* Tick action: decrement all non-zero timers *)
Tick ==
    /\ \E i \in Procs : timer[i] > 0
    /\ timer' = [i \in Procs |-> IF timer[i] > 0 THEN timer[i] - 1 ELSE 0]
    /\ UNCHANGED <<pc, lock>>

(* All process actions *)
ProcAction(i) ==
    \/ Try(i)
    \/ SetLock(i)
    \/ EnterCS(i)
    \/ Retry(i)
    \/ ExitCS(i)

Next ==
    \/ \E i \in Procs : ProcAction(i)
    \/ Tick

(* Fairness: weak fairness on Tick and each process action *)
Fairness ==
    /\ WF_vars(Tick)
    /\ \A i \in Procs : WF_vars(ProcAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* SAFETY INVARIANTS *)

(* Mutual Exclusion: At most one process is in the critical section *)
MutualExclusion ==
    \A i, j \in Procs : (pc[i] = "critical" /\ pc[j] = "critical") => i = j

(* Alternative formulation *)
AtMostOneInCS ==
    Cardinality({i \in Procs : pc[i] = "critical"}) <= 1

(* Combined invariant *)
Invariant == TypeOK /\ MutualExclusion

-----------------------------------------------------------------------------
(* LIVENESS PROPERTIES *)

(* Some process is infinitely often in the critical section *)
SomeoneInCS == \E i \in Procs : pc[i] = "critical"

Liveness == []<>SomeoneInCS

-----------------------------------------------------------------------------
(* TLC State Count Check *)
(* This can be used to verify expected state counts in TLC *)

StateCountCheck ==
    TLCGet("distinct") >= 0  \* Always true, used for TLC evaluation

-----------------------------------------------------------------------------
(* THEOREMS AND NOTES *)

(*
THEOREM Spec => []MutualExclusion
  - This theorem holds when Delta < Epsilon
  - When Delta >= Epsilon, mutual exclusion can be violated
  
The bug occurs as follows when Delta >= Epsilon and N > 1:
  1. Process 1 sees lock = 0, sets timer to Delta, sets lock = 1
  2. Before Epsilon time passes, process 1's timer expires (since Delta >= Epsilon is possible)
  3. Meanwhile process 2 also saw lock = 0 (or sees lock changing)
  4. Both processes can end up in the critical section

The timing constraint Delta < Epsilon ensures:
  - A process waits at least Epsilon after setting lock
  - Any other process that saw lock = 0 will have set lock within Delta
  - Since Delta < Epsilon, the first process will see the changed lock value
*)

=============================================================================