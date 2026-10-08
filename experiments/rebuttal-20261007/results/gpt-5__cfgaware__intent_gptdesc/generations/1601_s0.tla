----------------------------- MODULE FischerTimed -----------------------------
EXTENDS Naturals, TLC

(*
  Timed mutual-exclusion (Fischer-style) with synchronous discrete ticks.
  Processes are 1..N. A single shared register 'mem' holds 0 (empty) or a pid.
  Each process uses a local countdown timer t[p] that is decremented by Tick.
  Two timing constants:
    - Delta  = long delay
    - Epsilon = short delay
  Requirement: Delta >= Epsilon
*)

CONSTANTS
  N,        \* number of processes
  Epsilon,  \* short delay
  Delta,    \* long delay
  Inf       \* sentinel for "disabled"/infinite timer

ASSUME
  /\ N \in Nat \ {0}
  /\ Epsilon \in Nat
  /\ Delta \in Nat
  /\ Delta >= Epsilon
  /\ Inf \notin Nat

(************** State and types **************)

Proc == 1..N
None == 0

TimerVal == Nat \cup {Inf}

VARIABLES
  mem,   \* shared register: None (=0) or some pid in Proc
  pc,    \* control state per process: "Idle", "WaitLong", "Resvd", "CS"
  t,     \* countdown timer per process in TimerVal
  want   \* whether a process is continuously attempting to enter
         \* (environment-controlled; may toggle nondeterministically)

vars == << mem, pc, t, want >>

TypeOK ==
  /\ mem \in {None} \cup Proc
  /\ pc \in [Proc -> {"Idle", "WaitLong", "Resvd", "CS"}]
  /\ t \in [Proc -> TimerVal]
  /\ want \in [Proc -> BOOLEAN]

(************** Initialization **************)

Init ==
  /\ mem = None
  /\ pc = [p \in Proc |-> "Idle"]
  /\ t  = [p \in Proc |-> Inf]
  /\ want \in [Proc -> BOOLEAN]

(************** Synchronous global time tick **************)

Tick ==
  /\ UNCHANGED << mem, pc, want >>
  /\ t' = [p \in Proc |-> IF t[p] = Inf THEN Inf
                         ELSE IF t[p] = 0 THEN 0
                         ELSE t[p] - 1]

(************** Per-process actions **************)

Start(p) ==
  /\ want[p]
  /\ pc[p] = "Idle"
  /\ pc' = [pc EXCEPT ![p] = "WaitLong"]
  /\ t'  = [t  EXCEPT ![p] = Delta]
  /\ UNCHANGED << mem, want >>

Reserve(p) ==
  /\ pc[p] = "WaitLong"
  /\ t[p] = 0
  /\ mem = None
  /\ mem' = p
  /\ pc'  = [pc EXCEPT ![p] = "Resvd"]
  /\ t'   = [t  EXCEPT ![p] = Epsilon]
  /\ UNCHANGED want

EnterCS(p) ==
  /\ pc[p] = "Resvd"
  /\ t[p] = 0
  /\ mem = p
  /\ pc' = [pc EXCEPT ![p] = "CS"]
  /\ UNCHANGED << mem, t, want >>

GiveUp(p) ==
  /\ pc[p] = "Resvd"
  /\ t[p] = 0
  /\ mem # p
  /\ pc' = [pc EXCEPT ![p] = "WaitLong"]
  /\ t'  = [t  EXCEPT ![p] = Delta]
  /\ UNCHANGED << mem, want >>

Exit(p) ==
  /\ pc[p] = "CS"
  /\ pc' = [pc EXCEPT ![p] = "Idle"]
  /\ mem' = None
  /\ UNCHANGED << t, want >>

ProcStep(p) ==
  Start(p) \/ Reserve(p) \/ EnterCS(p) \/ GiveUp(p) \/ Exit(p)

(*
  Environment may toggle whether a process is trying.
  Not included in fairness; used to express "continuously attempts entry".
*)
ToggleWant(p) ==
  /\ want' = [want EXCEPT ![p] = ~ want[p]]
  /\ UNCHANGED << mem, pc, t >>

Next ==
  \/ Tick
  \/ \E p \in Proc : ProcStep(p)
  \/ \E p \in Proc : ToggleWant(p)

(************** Safety: mutual exclusion **************)

MutualExclusion ==
  \A p, q \in Proc : p # q => ~(pc[p] = "CS" /\ pc[q] = "CS")

Invariant == MutualExclusion

(************** Fairness and overall specification **************)

Fairness ==
  /\ SF_vars(Tick)
  /\ \A p \in Proc : SF_vars( want[p] /\ ProcStep(p) )

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

(************** Required liveness property **************)

(*
  If a process continuously attempts entry (want[p] holds), then it eventually enters CS.
  This is stated as a property to be checked under Spec (which already includes fairness).
*)
Liveness ==
  \A p \in Proc : []( want[p] => <> (pc[p] = "CS") )

(************** Additional checkable witness properties (optional) **************)

BadME ==
  <> (\E p, q \in Proc : p # q /\ pc[p] = "CS" /\ pc[q] = "CS")

ClaimedButNeverEnters(p) ==
  <>[] (pc[p] = "Resvd" /\ t[p] = 0 /\ mem = p)

=============================================================================