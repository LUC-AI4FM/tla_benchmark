------------------------------ MODULE EPFailureDetectorSystem ------------------------------
(***************************************************************************)
(* A parameterized, partially synchronous distributed system with eventually*)
(* perfect failure detectors (Chandra & Toueg).                            *)
(*                                                                         *)
(* The two parts of the system are written inline in this one module:      *)
(*   - Age_Channel part: messages in transit carry an age.  The environment *)
(*     tick (global clock) ages every in-transit message.                  *)
(*   - EPFailureDetector part: the behavior of correct processes.  Each    *)
(*     process periodically sends "alive" messages (at SendPoint of its    *)
(*     local step cycle).  It periodically predicts failures (at           *)
(*     PredictPoint), suspecting peers not heard from within their timeout. *)
(*     A process that finds out a suspicion was false removes it and       *)
(*     increases that peer's timeout.                                      *)
(*                                                                         *)
(* Partial synchrony is enforced by the following constraints on the       *)
(* global Tick:                                                            *)
(*   DELTAConstraint: no message may stay in transit longer than DELTA.    *)
(*   PHIConstraint  : no correct process may stay idle longer than PHI     *)
(*                    global ticks.                                        *)
(*                                                                         *)
(* Clocks are encoded modulo/capped so the state space stays finite for    *)
(* fixed parameters.  Timeouts can still grow, so StateConstraint bounds   *)
(* them.  Bounding them avoids state explosion when running TLC on small   *)
(* instances.                                                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,             \* number of processes
          T,             \* maximum number of crashed processes
          d0,            \* initial timeout value
          SendPoint,     \* local step at which "alive" messages are sent
          PredictPoint,  \* local step at which failures are predicted
          DELTA,         \* bound on message delay (in global ticks)
          PHI            \* bound on relative process speed (in global ticks)

ASSUME /\ N \in Nat \ {0}
       /\ T \in 0..N
       /\ d0 \in Nat
       /\ SendPoint \in Nat
       /\ PredictPoint \in Nat
       /\ DELTA \in Nat \ {0}
       /\ PHI \in Nat \ {0}

Procs == 1..N

Cycle == IF SendPoint >= PredictPoint THEN SendPoint ELSE PredictPoint

TimeoutBound == d0 + (Cycle + 1) * PHI + DELTA + 1

VARIABLES
    alive,          \* alive[p] : p has not crashed
    msgs,           \* msgs[s][r] : set of ages of "alive" messages from s to r in transit
    lclock,         \* local step counter of each process (mod Cycle+1)
    idle,           \* idle[p] : global ticks since p last took a step
    fromLastHeard,  \* fromLastHeard[p][q] : global ticks since p last heard from q (capped)
    timeout,        \* timeout[p][q] : p's current timeout for q
    suspected       \* suspected[p] : set of processes p suspects

vars == <<alive, msgs, lclock, idle, fromLastHeard, timeout, suspected>>

TypeOK ==
    /\ alive \in [Procs -> BOOLEAN]
    /\ msgs \in [Procs -> [Procs -> SUBSET (0..DELTA)]]
    /\ lclock \in [Procs -> 0..Cycle]
    /\ idle \in [Procs -> 0..PHI]
    /\ fromLastHeard \in [Procs -> [Procs -> Nat]]
    /\ timeout \in [Procs -> [Procs -> Nat]]
    /\ suspected \in [Procs -> SUBSET Procs]

Init ==
    /\ alive = [p \in Procs |-> TRUE]
    /\ msgs = [s \in Procs |-> [r \in Procs |-> {}]]
    /\ lclock = [p \in Procs |-> 0]
    /\ idle = [p \in Procs |-> 0]
    /\ fromLastHeard = [p \in Procs |-> [q \in Procs |-> 0]]
    /\ timeout = [p \in Procs |-> [q \in Procs |-> d0]]
    /\ suspected = [p \in Procs |-> {}]

NumCrashed == Cardinality({p \in Procs : ~alive[p]})

(***************************************************************************)
(* Environment: crash of a process (at most T crashes).                    *)
(***************************************************************************)
Crash(p) ==
    /\ alive[p]
    /\ NumCrashed < T
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ msgs' = [s \in Procs |-> [r \in Procs |-> IF r = p THEN {} ELSE msgs[s][r]]]
    /\ UNCHANGED <<lclock, idle, fromLastHeard, timeout, suspected>>

(***************************************************************************)
(* Partial synchrony constraints restricting the global tick.              *)
(***************************************************************************)
DELTAConstraint == \A s, r \in Procs : DELTA \notin msgs[s][r]

PHIConstraint == \A p \in Procs : alive[p] => idle[p] < PHI

(***************************************************************************)
(* Environment: global clock tick; ages messages and local timers.         *)
(***************************************************************************)
Tick ==
    /\ DELTAConstraint
    /\ PHIConstraint
    /\ msgs' = [s \in Procs |-> [r \in Procs |->
                   IF alive[r] THEN {a + 1 : a \in msgs[s][r]} ELSE {}]]
    /\ idle' = [p \in Procs |-> IF alive[p] THEN idle[p] + 1 ELSE idle[p]]
    /\ fromLastHeard' = [p \in Procs |-> [q \in Procs |->
                   IF alive[p] /\ fromLastHeard[p][q] <= timeout[p][q]
                     THEN fromLastHeard[p][q] + 1
                     ELSE fromLastHeard[p][q]]]
    /\ UNCHANGED <<alive, lclock, timeout, suspected>>

(***************************************************************************)
(* A step of a correct process p (EPFailureDetector part): receive some    *)
(* messages, which must include every message that has reached the maximal *)
(* age DELTA.  Then fix false suspicions, possibly send alive messages, and *)
(* possibly predict failures.                                              *)
(***************************************************************************)
Step(p) ==
    /\ alive[p]
    /\ \E S \in SUBSET {q \in Procs \ {p} : msgs[q][p] # {}} :
        /\ {q \in Procs : DELTA \in msgs[q][p]} \subseteq S
        /\ LET sendNow    == lclock[p] = SendPoint
               predictNow == lclock[p] = PredictPoint
               wrong      == S \cap suspected[p]
               newHeard   == [q \in Procs |->
                               IF q \in S THEN 0 ELSE fromLastHeard[p][q]]
               newTimeout == [q \in Procs |->
                               IF q \in wrong THEN timeout[p][q] + 1
                                              ELSE timeout[p][q]]
               kept       == suspected[p] \ S
               newSusp    == IF predictNow
                               THEN kept \cup {q \in Procs \ {p} :
                                                 newHeard[q] > newTimeout[q]}
                               ELSE kept
           IN /\ msgs' = [s \in Procs |-> [r \in Procs |->
                             IF r = p /\ s \in S THEN {}
                             ELSE IF s = p /\ r # p /\ sendNow /\ alive[r]
                                    THEN msgs[s][r] \cup {0}
                                    ELSE msgs[s][r]]]
              /\ fromLastHeard' = [fromLastHeard EXCEPT ![p] = newHeard]
              /\ timeout' = [timeout EXCEPT ![p] = newTimeout]
              /\ suspected' = [suspected EXCEPT ![p] = newSusp]
    /\ lclock' = [lclock EXCEPT ![p] = IF lclock[p] = Cycle THEN 0 ELSE lclock[p] + 1]
    /\ idle' = [idle EXCEPT ![p] = 0]
    /\ UNCHANGED alive

Next ==
    \/ Tick
    \/ \E p \in Procs : Crash(p)
    \/ \E p \in Procs : Step(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Tick)
    /\ \A p \in Procs : WF_vars(Step(p))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* Strong Completeness: every crashed process is eventually permanently
\* suspected by every correct process.
StrongCompleteness ==
    \A p, q \in Procs :
        <>[]((alive[p] /\ ~alive[q]) => q \in suspected[p])

\* Eventually Strong Accuracy: eventually no correct process is suspected
\* by any correct process.
EventuallyStrongAccuracy ==
    <>[](\A p, q \in Procs :
            (alive[p] /\ alive[q]) => q \notin suspected[p])

\* A correct process is never permanently suspected by a correct process.
NeverPermanentlySuspected ==
    \A p, q \in Procs :
        ~ <>[](alive[p] /\ alive[q] /\ q \in suspected[p])

(***************************************************************************)
(* State constraint for TLC: keeps the growing timeouts bounded.           *)
(***************************************************************************)
StateConstraint ==
    \A p, q \in Procs : timeout[p][q] <= TimeoutBound

==========================================================================================