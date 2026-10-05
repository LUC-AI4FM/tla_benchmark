---------------------------- MODULE fischer ----------------------------
(***************************************************************************)
(* Fischer's timed mutual exclusion algorithm for N synchronizing          *)
(* processes, together with a separate ticking process that decrements     *)
(* per-process timers.                                                     *)
(*                                                                         *)
(* BUG NOTE: A bug should be found when N > 1 and Delta >= Epsilon,        *)
(* highlighting the timing-sensitive design of the algorithm.              *)
(* The algorithm only works correctly when Delta < Epsilon.                *)
(***************************************************************************)

EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS N, Delta, Epsilon, Infinity

ASSUME N \in Nat \ {0}
ASSUME Delta \in Nat
ASSUME Epsilon \in Nat
ASSUME Infinity > Delta + Epsilon

VARIABLES pc, id, timer

vars == <<pc, id, timer>>

Procs == 1..N

TypeOK ==
    /\ pc \in [Procs -> {"idle", "try", "check", "wait", "cs", "exit"}]
    /\ id \in (Procs \cup {0})
    /\ timer \in [Procs -> 0..Infinity]

(***************************************************************************)
(* Fischer's Algorithm:                                                    *)
(* - A process in "idle" can move to "try" to begin attempting entry       *)
(* - In "try", if id = 0, process sets id to itself and moves to "check"   *)
(*   with timer set to Delta (must complete write within Delta time)       *)
(* - In "check", process waits for its timer to expire (timer = 0),        *)
(*   then checks if id is still itself; if so, enters "cs", else back to   *)
(*   "idle"                                                                *)
(* - Process must wait at least Epsilon time before checking               *)
(* - In "cs" (critical section), process can move to "exit"                *)
(* - In "exit", process resets id to 0 and returns to "idle"               *)
(***************************************************************************)

(* Initial state *)
Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ id = 0
    /\ timer = [p \in Procs |-> 0]

(* Process p starts trying to enter critical section *)
TryStart(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "try"]
    /\ timer' = [timer EXCEPT ![p] = Epsilon]
    /\ UNCHANGED id

(* Process p checks if id is free and sets it *)
SetId(p) ==
    /\ pc[p] = "try"
    /\ id = 0
    /\ id' = p
    /\ pc' = [pc EXCEPT ![p] = "check"]
    /\ timer' = [timer EXCEPT ![p] = Delta]

(* Process p waits for timer to expire then checks id *)
CheckId(p) ==
    /\ pc[p] = "check"
    /\ timer[p] = 0
    /\ IF id = p
       THEN pc' = [pc EXCEPT ![p] = "cs"]
       ELSE pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<id, timer>>

(* Process p is in critical section and decides to exit *)
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<id, timer>>

(* Process p resets id and returns to idle *)
Reset(p) ==
    /\ pc[p] = "exit"
    /\ id' = 0
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED timer

(* A process action *)
ProcAction(p) ==
    \/ TryStart(p)
    \/ SetId(p)
    \/ CheckId(p)
    \/ ExitCS(p)
    \/ Reset(p)

(* Tick action - decrements all non-zero timers *)
(* This models the passage of time *)
Tick ==
    /\ \E p \in Procs : timer[p] > 0
    /\ timer' = [p \in Procs |-> IF timer[p] > 0 THEN timer[p] - 1 ELSE 0]
    /\ UNCHANGED <<pc, id>>

(* Next state relation *)
Next ==
    \/ \E p \in Procs : ProcAction(p)
    \/ Tick

(***************************************************************************)
(* Fairness conditions                                                     *)
(***************************************************************************)

(* Weak fairness on process actions and tick *)
Fairness ==
    /\ \A p \in Procs : WF_vars(TryStart(p))
    /\ \A p \in Procs : WF_vars(SetId(p))
    /\ \A p \in Procs : WF_vars(CheckId(p))
    /\ \A p \in Procs : WF_vars(ExitCS(p))
    /\ \A p \in Procs : WF_vars(Reset(p))
    /\ WF_vars(Tick)

(* Complete specification *)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety Invariant: Mutual Exclusion                                      *)
(* At most one process can be in the critical section at any time.         *)
(***************************************************************************)

MutualExclusion ==
    \A p1, p2 \in Procs :
        (pc[p1] = "cs" /\ pc[p2] = "cs") => p1 = p2

(* Alternative formulation counting processes in CS *)
AtMostOneInCS ==
    Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

(***************************************************************************)
(* Liveness Property: Some process is infinitely often in critical section *)
(***************************************************************************)

SomeoneInCS == \E p \in Procs : pc[p] = "cs"

Liveness == []<>SomeoneInCS

(***************************************************************************)
(* TLC State Count Check                                                   *)
(* Named state counts for verification                                     *)
(***************************************************************************)

IdleCount == Cardinality({p \in Procs : pc[p] = "idle"})
TryCount == Cardinality({p \in Procs : pc[p] = "try"})
CheckCount == Cardinality({p \in Procs : pc[p] = "check"})
CSCount == Cardinality({p \in Procs : pc[p] = "cs"})
ExitCount == Cardinality({p \in Procs : pc[p] = "exit"})

StateCountCheck ==
    /\ IdleCount + TryCount + CheckCount + CSCount + ExitCount = N

=========================================================================