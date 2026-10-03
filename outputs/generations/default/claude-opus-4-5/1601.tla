---------------------------- MODULE Fischer ----------------------------
(***************************************************************************)
(* Fischer's timed mutual exclusion algorithm for N synchronizing          *)
(* processes, together with a separate ticking process that decrements     *)
(* per-process timers.                                                     *)
(*                                                                         *)
(* NOTE: A bug should be found when N > 1 and Delta >= Epsilon,            *)
(* highlighting the timing-sensitive design of the algorithm.              *)
(* The algorithm is correct only when Delta < Epsilon.                     *)
(***************************************************************************)

EXTENDS Naturals, Integers, TLC, FiniteSets

CONSTANTS N,           \* Number of processes
          Delta,       \* Maximum time to write id
          Epsilon,     \* Minimum time to wait before entering CS
          Infinity     \* Large sentinel value for "infinite" timer

ASSUME N \in Nat /\ N >= 1
ASSUME Delta \in Nat /\ Delta >= 0
ASSUME Epsilon \in Nat /\ Epsilon >= 0
ASSUME Infinity \in Nat /\ Infinity > Delta /\ Infinity > Epsilon

VARIABLES pc,          \* Program counter for each process: "idle", "try", "wait", "check", "cs"
          id,          \* Shared variable holding the id of the last process to write
          timer,       \* Per-process timer (countdown)
          tickTimer    \* Global tick timer to control time advancement

vars == <<pc, id, timer, tickTimer>>

Procs == 1..N

(***************************************************************************)
(* PlusCal Algorithm (conceptual):                                         *)
(*                                                                         *)
(* --algorithm Fischer {                                                   *)
(*   variables id = 0;                                                     *)
(*                                                                         *)
(*   process (P \in 1..N)                                                  *)
(*   variables timer = Infinity;                                           *)
(*   {                                                                     *)
(*     idle: while (TRUE) {                                                *)
(*       try:  await id = 0;                                               *)
(*             id := self;                                                 *)
(*             timer := Delta;                                             *)
(*       wait: await timer = 0;                                            *)
(*       check: if (id = self) {                                           *)
(*         cs:    skip; \* critical section                                *)
(*                id := 0;                                                 *)
(*                goto idle;                                               *)
(*              } else {                                                   *)
(*                goto idle;                                               *)
(*              }                                                          *)
(*     }                                                                   *)
(*   }                                                                     *)
(*                                                                         *)
(*   process (Tick = 0)                                                    *)
(*   {                                                                     *)
(*     tick: while (TRUE) {                                                *)
(*             \* Decrement all timers by 1 (but not below 0)              *)
(*             with (decremented timers) { ... }                           *)
(*           }                                                             *)
(*   }                                                                     *)
(* }                                                                       *)
(***************************************************************************)

TypeOK ==
    /\ pc \in [Procs -> {"idle", "try", "wait", "check", "cs"}]
    /\ id \in 0..N
    /\ timer \in [Procs -> 0..Infinity]
    /\ tickTimer \in {0, 1}

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ id = 0
    /\ timer = [p \in Procs |-> Infinity]
    /\ tickTimer = 1

(***************************************************************************)
(* Process P actions                                                       *)
(***************************************************************************)

\* Process p moves from idle to try
Idle(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "try"]
    /\ UNCHANGED <<id, timer, tickTimer>>

\* Process p tries: waits for id = 0, then sets id to self and starts timer
Try(p) ==
    /\ pc[p] = "try"
    /\ id = 0
    /\ id' = p
    /\ timer' = [timer EXCEPT ![p] = Delta]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED tickTimer

\* Process p waits for timer to reach 0, then sets timer to Epsilon for check
Wait(p) ==
    /\ pc[p] = "wait"
    /\ timer[p] = 0
    /\ timer' = [timer EXCEPT ![p] = Epsilon]
    /\ pc' = [pc EXCEPT ![p] = "check"]
    /\ UNCHANGED <<id, tickTimer>>

\* Process p checks if id = self; if so, enters CS; otherwise, back to idle
Check(p) ==
    /\ pc[p] = "check"
    /\ timer[p] = 0
    /\ IF id = p
       THEN pc' = [pc EXCEPT ![p] = "cs"]
       ELSE pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<id, timer, tickTimer>>

\* Process p is in critical section; exits and resets id
CS(p) ==
    /\ pc[p] = "cs"
    /\ id' = 0
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ timer' = [timer EXCEPT ![p] = Infinity]
    /\ UNCHANGED tickTimer

\* Combined process action for process p
ProcAction(p) ==
    \/ Idle(p)
    \/ Try(p)
    \/ Wait(p)
    \/ Check(p)
    \/ CS(p)

(***************************************************************************)
(* Tick process: decrements all timers by 1 (but not below 0)              *)
(***************************************************************************)

\* Helper to decrement timer value
Decrement(t) == IF t > 0 /\ t < Infinity THEN t - 1 ELSE t

Tick ==
    /\ tickTimer = 1
    /\ timer' = [p \in Procs |-> Decrement(timer[p])]
    /\ tickTimer' = 1
    /\ UNCHANGED <<pc, id>>

(***************************************************************************)
(* Next state relation                                                     *)
(***************************************************************************)
Next ==
    \/ \E p \in Procs : ProcAction(p)
    \/ Tick

(***************************************************************************)
(* Fairness conditions                                                     *)
(***************************************************************************)
Fairness ==
    /\ \A p \in Procs : WF_vars(ProcAction(p))
    /\ WF_vars(Tick)

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety Invariant: Mutual Exclusion                                      *)
(* At most one process is in the critical section at any time              *)
(***************************************************************************)
MutualExclusion ==
    \A p1, p2 \in Procs : (pc[p1] = "cs" /\ pc[p2] = "cs") => p1 = p2

\* Alternative formulation
InCS == {p \in Procs : pc[p] = "cs"}
MutexInvariant == Cardinality(InCS) <= 1

(***************************************************************************)
(* Liveness Property: Some process is infinitely often in the CS           *)
(***************************************************************************)
SomeoneInCS == \E p \in Procs : pc[p] = "cs"
Liveness == []<>SomeoneInCS

(***************************************************************************)
(* TLC-based state count check (for debugging/verification)                *)
(***************************************************************************)
StateCount ==
    /\ TLCGet("distinct") >= 0

(***************************************************************************)
(* Theorems to check                                                       *)
(***************************************************************************)
THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness

=========================================================================