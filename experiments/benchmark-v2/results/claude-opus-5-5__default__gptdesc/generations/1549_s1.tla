---------------------------- MODULE EPFailureDetectorSystem ----------------------------
(***************************************************************************)
(* A parameterized, partially synchronous system with an eventually       *)
(* perfect failure detector (Chandra & Toueg).  This module inlines two    *)
(* components so that it stands alone:                                     *)
(*   - Age_Channel : point-to-point channels whose in-transit messages     *)
(*                   carry an age, i.e. the number of global ticks since   *)
(*                   they were sent.                                       *)
(*   - EPFailureDetector : correct processes cycle through SEND, RCV and   *)
(*                   COMP.  They send heartbeats, receive messages, and    *)
(*                   update their suspicions and timeouts.                 *)
(*                                                                         *)
(* Clocks are relative so the state space stays finite once the constants *)
(* are fixed:                                                              *)
(*   - Each message age is bounded by DELTA (DELTAConstraint).             *)
(*   - Each alive process has a "pause" counter, the number of global      *)
(*     ticks since its last COMP step, bounded by PHI (PHIConstraint).     *)
(*   - Local timers ("waiting") count a process's own steps since it last  *)
(*     heard from a peer.  They are capped by the timeout, which grows     *)
(*     only after a false suspicion.                                       *)
(* The global clock advances through Tick.  Tick is enabled only when it   *)
(* would not violate DELTA or PHI.  This is how partial synchrony is       *)
(* encoded.  Each process completes at most one SEND/RCV/COMP cycle per    *)
(* tick, so local clocks stay comparable with global time.                 *)
(*                                                                         *)
(* Note: with TLC, the state space grows quickly in DELTA and PHI because  *)
(* every channel holds a set of ages.  Check only small instances, such as *)
(* N = 2 or 3, T = 1, DELTA = 1 and PHI = 1.                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,       \* number of processes
          T,       \* maximum number of crashes
          d0,      \* initial timeout value
          DELTA,   \* bound on message delay (in global ticks)
          PHI      \* bound on relative process speed (in global ticks)

ASSUME /\ N \in Nat \ {0}
       /\ T \in 0..N
       /\ d0 \in Nat
       /\ DELTA \in Nat
       /\ PHI \in Nat \ {0}

Proc == 1..N

VARIABLES
  alive,      \* alive[p]          : p has not crashed
  nCrashed,   \* number of crashed processes
  pc,         \* pc[p] \in {"SEND","RCV","COMP"}
  msgs,       \* msgs[s][r]        : set of ages of in-transit messages s -> r
  rcvd,       \* rcvd[p][q]        : p received a message from q in this cycle
  waiting,    \* waiting[p][q]     : local clock of p since it last heard from q
  timeout,    \* timeout[p][q]     : current timeout p uses for q
  suspected,  \* suspected[p]      : set of processes suspected by p
  pause,      \* pause[p]          : global ticks since p's last COMP step
  done        \* done[p]           : p finished a cycle in the current tick

vars == << alive, nCrashed, pc, msgs, rcvd, waiting, timeout,
           suspected, pause, done >>

---------------------------------------------------------------------------
(* Type invariant *)
TypeOK ==
  /\ alive \in [Proc -> BOOLEAN]
  /\ nCrashed \in 0..T
  /\ pc \in [Proc -> {"SEND", "RCV", "COMP"}]
  /\ msgs \in [Proc -> [Proc -> SUBSET (0..DELTA)]]
  /\ rcvd \in [Proc -> [Proc -> BOOLEAN]]
  /\ waiting \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspected \in [Proc -> SUBSET Proc]
  /\ pause \in [Proc -> 0..PHI]
  /\ done \in [Proc -> BOOLEAN]

(* Partial synchrony constraints *)
DELTAConstraint ==
  \A s, r \in Proc : alive[r] => \A a \in msgs[s][r] : a <= DELTA

PHIConstraint ==
  \A p \in Proc : alive[p] => pause[p] <= PHI

---------------------------------------------------------------------------
Init ==
  /\ alive = [p \in Proc |-> TRUE]
  /\ nCrashed = 0
  /\ pc = [p \in Proc |-> "SEND"]
  /\ msgs = [s \in Proc |-> [r \in Proc |-> {}]]
  /\ rcvd = [p \in Proc |-> [q \in Proc |-> FALSE]]
  /\ waiting = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ suspected = [p \in Proc |-> {}]
  /\ pause = [p \in Proc |-> 0]
  /\ done = [p \in Proc |-> FALSE]

---------------------------------------------------------------------------
(* Environment: a process crashes.  Messages addressed to it are dropped. *)
Crash(p) ==
  /\ alive[p]
  /\ nCrashed < T
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ nCrashed' = nCrashed + 1
  /\ msgs' = [s \in Proc |-> [r \in Proc |->
                IF r = p THEN {} ELSE msgs[s][r]]]
  /\ UNCHANGED << pc, rcvd, waiting, timeout, suspected, pause, done >>

(* Environment: global clock tick.  Messages and pauses age.             *)
(* Tick is enabled only if the step preserves DELTA and PHI.             *)
Tick ==
  /\ \A p \in Proc : alive[p] => pause[p] < PHI
  /\ \A s, r \in Proc : alive[r] => \A a \in msgs[s][r] : a < DELTA
  /\ msgs' = [s \in Proc |-> [r \in Proc |-> {a + 1 : a \in msgs[s][r]}]]
  /\ pause' = [p \in Proc |-> IF alive[p] THEN pause[p] + 1 ELSE pause[p]]
  /\ done' = [p \in Proc |-> FALSE]
  /\ UNCHANGED << alive, nCrashed, pc, rcvd, waiting, timeout, suspected >>

---------------------------------------------------------------------------
(* EPFailureDetector: behavior of correct processes *)

(* p broadcasts a heartbeat ("alive") with age 0 to every other process. *)
Send(p) ==
  /\ alive[p]
  /\ pc[p] = "SEND"
  /\ ~done[p]
  /\ msgs' = [s \in Proc |-> [r \in Proc |->
                IF s = p /\ r # p /\ alive[r]
                  THEN msgs[s][r] \cup {0}
                  ELSE msgs[s][r]]]
  /\ pc' = [pc EXCEPT ![p] = "RCV"]
  /\ UNCHANGED << alive, nCrashed, rcvd, waiting, timeout, suspected,
                  pause, done >>

(* p receives every message on some set S of incoming channels.          *)
(* A channel holding a message of age DELTA must be in S.                *)
Receive(p) ==
  /\ alive[p]
  /\ pc[p] = "RCV"
  /\ \E S \in SUBSET {q \in Proc : msgs[q][p] # {}} :
       /\ \A q \in Proc : DELTA \in msgs[q][p] => q \in S
       /\ msgs' = [s \in Proc |-> [r \in Proc |->
                     IF r = p /\ s \in S THEN {} ELSE msgs[s][r]]]
       /\ rcvd' = [rcvd EXCEPT ![p] = [q \in Proc |-> q \in S]]
  /\ pc' = [pc EXCEPT ![p] = "COMP"]
  /\ UNCHANGED << alive, nCrashed, waiting, timeout, suspected, pause, done >>

(* p updates its local timers, suspicions and timeouts.                  *)
Comp(p) ==
  /\ alive[p]
  /\ pc[p] = "COMP"
  /\ suspected' = [suspected EXCEPT ![p] =
        {q \in Proc \ {p} :
           IF rcvd[p][q]
             THEN FALSE
             ELSE \/ q \in suspected[p]
                  \/ waiting[p][q] + 1 > timeout[p][q]}]
  /\ timeout' = [timeout EXCEPT ![p] =
        [q \in Proc |->
           IF rcvd[p][q] /\ q \in suspected[p]
             THEN timeout[p][q] + 1
             ELSE timeout[p][q]]]
  /\ waiting' = [waiting EXCEPT ![p] =
        [q \in Proc |->
           IF q = p \/ rcvd[p][q] THEN 0
           ELSE IF q \in suspected[p] THEN waiting[p][q]
           ELSE waiting[p][q] + 1]]
  /\ rcvd' = [rcvd EXCEPT ![p] = [q \in Proc |-> FALSE]]
  /\ pc' = [pc EXCEPT ![p] = "SEND"]
  /\ pause' = [pause EXCEPT ![p] = 0]
  /\ done' = [done EXCEPT ![p] = TRUE]
  /\ UNCHANGED << alive, nCrashed, msgs >>

ProcStep(p) == Send(p) \/ Receive(p) \/ Comp(p)

---------------------------------------------------------------------------
Next ==
  \/ Tick
  \/ \E p \in Proc : Crash(p)
  \/ \E p \in Proc : ProcStep(p)

Fairness ==
  /\ WF_vars(Tick)
  /\ \A p \in Proc : WF_vars(ProcStep(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety invariants *)
Invariants == TypeOK /\ DELTAConstraint /\ PHIConstraint

(* Strong Completeness: every crashed process is eventually permanently  *)
(* suspected by every correct process.                                    *)
StrongCompleteness ==
  <>[](\A p, q \in Proc :
          (alive[p] /\ ~alive[q]) => q \in suspected[p])

(* Eventually Strong Accuracy: eventually no correct process is          *)
(* suspected by any correct process.                                      *)
EventuallyStrongAccuracy ==
  <>[](\A p, q \in Proc :
          (alive[p] /\ alive[q]) => q \notin suspected[p])

THEOREM Spec => []Invariants
THEOREM Spec => StrongCompleteness /\ EventuallyStrongAccuracy
=============================================================================