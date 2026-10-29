---------------------------- MODULE EP_ChandraToueg ----------------------------
(***************************************************************************)
(* A parameterized, partially synchronous system with eventually perfect   *)
(* failure detectors, after Chandra and Toueg.  This single module inlines *)
(* the two components so that it parses on its own:                        *)
(*                                                                         *)
(*  - Age_Channel: every in-transit "alive" message carries an age that    *)
(*    grows by one at each global tick.  DELTAConstraint forbids a tick    *)
(*    while a message to a live process already has age DELTA.  Such a     *)
(*    message must therefore be delivered first.                           *)
(*                                                                         *)
(*  - EPFailureDetector: each process cycles SEND -> RECEIVE -> COMP.      *)
(*    It sends heartbeats every SendPoint local steps.  It suspects a      *)
(*    silent peer when the waiting time exceeds the timeout for that peer. *)
(*    It raises the timeout after each false suspicion.                    *)
(*                                                                         *)
(* Clocks are encoded relatively so that the state space stays finite.     *)
(* The global clock is only implicit in the Tick action.  Each process     *)
(* has a bounded local clock in 0..SendPoint, plus a "moved" counter that  *)
(* records how many ticks have passed since its last step.                 *)
(* PHIConstraint forbids a tick while a live process has gone PHI ticks    *)
(* without a step.                                                         *)
(*                                                                         *)
(* Message ages are bounded by DELTA, idle times by PHI and timeouts by    *)
(* TO_MAX, so TLC can check small instances.  Note that large values of    *)
(* DELTA and PHI cause a severe state explosion.  This is because the      *)
(* interleavings of ticks and process steps multiply quickly.              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,          \* number of processes
    T,          \* maximum number of crashes
    DELTA,      \* bound on message delay (in global ticks)
    PHI,        \* bound on relative process speed (in global ticks)
    SendPoint,  \* a process sends heartbeats every SendPoint local steps
    TO_INIT,    \* initial timeout value
    TO_MAX      \* cap on timeouts (keeps the state space finite)

ASSUME /\ N \in Nat \ {0}
       /\ T \in 0..N
       /\ DELTA \in Nat \ {0}
       /\ PHI \in Nat \ {0}
       /\ SendPoint \in Nat \ {0}
       /\ TO_INIT \in Nat
       /\ TO_MAX \in Nat
       /\ TO_INIT <= TO_MAX

Procs == 1..N

Min(a, b) == IF a <= b THEN a ELSE b

VARIABLES
    alive,        \* alive[i] : process i has not crashed
    pc,           \* pc[i] \in {"SEND","RECEIVE","COMP"}
    localClock,   \* local clock of i, in 0..SendPoint
    moved,        \* number of global ticks since i's last step
    msgs,         \* msgs[i][j] : set of ages of messages in transit from i to j
    heard,        \* heard[i][j] : i got a message from j in the current round
    waitingTime,  \* waitingTime[i][j] : rounds since i last heard from j
    timeout,      \* timeout[i][j] : current timeout of i for j
    suspected     \* suspected[i] : set of processes that i suspects

chanVars == <<msgs>>
envVars  == <<alive, moved>>
procVars == <<pc, localClock, heard, waitingTime, timeout, suspected>>
vars     == <<alive, pc, localClock, moved, msgs, heard,
              waitingTime, timeout, suspected>>

NumCrashed == Cardinality({i \in Procs : ~alive[i]})

-----------------------------------------------------------------------------
TypeOK ==
    /\ alive \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"SEND", "RECEIVE", "COMP"}]
    /\ localClock \in [Procs -> 0..SendPoint]
    /\ moved \in [Procs -> 0..PHI]
    /\ msgs \in [Procs -> [Procs -> SUBSET (0..DELTA)]]
    /\ heard \in [Procs -> [Procs -> BOOLEAN]]
    /\ waitingTime \in [Procs -> [Procs -> 0..(TO_MAX + 1)]]
    /\ timeout \in [Procs -> [Procs -> 0..TO_MAX]]
    /\ suspected \in [Procs -> SUBSET Procs]

Init ==
    /\ alive = [i \in Procs |-> TRUE]
    /\ pc = [i \in Procs |-> "SEND"]
    /\ localClock = [i \in Procs |-> 0]
    /\ moved = [i \in Procs |-> 0]
    /\ msgs = [i \in Procs |-> [j \in Procs |-> {}]]
    /\ heard = [i \in Procs |-> [j \in Procs |-> FALSE]]
    /\ waitingTime = [i \in Procs |-> [j \in Procs |-> 0]]
    /\ timeout = [i \in Procs |-> [j \in Procs |-> TO_INIT]]
    /\ suspected = [i \in Procs |-> {}]

-----------------------------------------------------------------------------
(* Environment: crashes and the global clock *)

Crash(k) ==
    /\ alive[k]
    /\ NumCrashed < T
    /\ alive' = [alive EXCEPT ![k] = FALSE]
    \* Messages addressed to a crashed process are lost.
    /\ msgs' = [i \in Procs |-> [j \in Procs |->
                   IF j = k THEN {} ELSE msgs[i][j]]]
    /\ UNCHANGED <<moved, procVars>>

\* Partial synchrony: no live receiver holds a message of age DELTA.
DELTAConstraint ==
    \A i, j \in Procs : alive[j] => \A a \in msgs[i][j] : a < DELTA

\* Partial synchrony: no live process has been idle for PHI ticks.
PHIConstraint ==
    \A i \in Procs : alive[i] => moved[i] < PHI

\* One global clock tick.  Messages age, and live processes grow idle.
Tick ==
    /\ DELTAConstraint
    /\ PHIConstraint
    /\ msgs' = [i \in Procs |-> [j \in Procs |->
                   IF alive[j] THEN {a + 1 : a \in msgs[i][j]} ELSE {}]]
    /\ moved' = [i \in Procs |->
                   IF alive[i] THEN moved[i] + 1 ELSE moved[i]]
    /\ UNCHANGED <<alive, procVars>>

-----------------------------------------------------------------------------
(* Process transitions (EPFailureDetector) *)

\* Every SendPoint local steps, send an "alive" message (age 0) to all others.
SendStep(i) ==
    /\ pc[i] = "SEND"
    /\ pc' = [pc EXCEPT ![i] = "RECEIVE"]
    /\ IF localClock[i] + 1 >= SendPoint
          THEN /\ localClock' = [localClock EXCEPT ![i] = 0]
               /\ msgs' = [msgs EXCEPT ![i] =
                     [j \in Procs |->
                        IF j # i /\ alive[j]
                           THEN msgs[i][j] \cup {0}
                           ELSE msgs[i][j]]]
          ELSE /\ localClock' = [localClock EXCEPT ![i] = localClock[i] + 1]
               /\ UNCHANGED msgs
    /\ moved' = [moved EXCEPT ![i] = 0]
    /\ UNCHANGED <<alive, heard, waitingTime, timeout, suspected>>

\* Receive the messages from some subset S of the senders.
\* Every buffer that holds a message of age DELTA must be in S.
ReceiveStep(i) ==
    /\ pc[i] = "RECEIVE"
    /\ \E S \in SUBSET {j \in Procs : msgs[j][i] # {}} :
         /\ \A j \in Procs : DELTA \in msgs[j][i] => j \in S
         /\ msgs' = [j \in Procs |-> [k \in Procs |->
                       IF k = i /\ j \in S THEN {} ELSE msgs[j][k]]]
         /\ heard' = [heard EXCEPT ![i] =
                       [j \in Procs |-> heard[i][j] \/ j \in S]]
    /\ pc' = [pc EXCEPT ![i] = "COMP"]
    /\ moved' = [moved EXCEPT ![i] = 0]
    /\ UNCHANGED <<alive, localClock, waitingTime, timeout, suspected>>

\* Update the suspicions.  A false suspicion raises the timeout for that peer.
CompStep(i) ==
    /\ pc[i] = "COMP"
    /\ suspected' = [suspected EXCEPT ![i] =
          {j \in Procs \ {i} :
             IF heard[i][j]
                THEN FALSE
                ELSE \/ j \in suspected[i]
                     \/ waitingTime[i][j] + 1 > timeout[i][j]}]
    /\ timeout' = [timeout EXCEPT ![i] =
          [j \in Procs |->
             IF heard[i][j] /\ j \in suspected[i]
                THEN Min(timeout[i][j] + 1, TO_MAX)
                ELSE timeout[i][j]]]
    /\ waitingTime' = [waitingTime EXCEPT ![i] =
          [j \in Procs |->
             IF heard[i][j] THEN 0
                            ELSE Min(waitingTime[i][j] + 1, TO_MAX + 1)]]
    /\ heard' = [heard EXCEPT ![i] = [j \in Procs |-> FALSE]]
    /\ pc' = [pc EXCEPT ![i] = "SEND"]
    /\ moved' = [moved EXCEPT ![i] = 0]
    /\ UNCHANGED <<alive, localClock, msgs>>

Step(i) ==
    /\ alive[i]
    /\ \/ SendStep(i)
       \/ ReceiveStep(i)
       \/ CompStep(i)

-----------------------------------------------------------------------------
Next ==
    \/ Tick
    \/ \E k \in Procs : Crash(k)
    \/ \E i \in Procs : Step(i)

Fairness ==
    /\ WF_vars(Tick)
    /\ \A i \in Procs : WF_vars(Step(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

\* Partial synchrony is never violated in a reachable state.
PartialSynchrony ==
    /\ \A i, j \in Procs : alive[j] => \A a \in msgs[i][j] : a <= DELTA
    /\ \A i \in Procs : alive[i] => moved[i] <= PHI

CrashBound == NumCrashed <= T

NoSelfSuspicion == \A i \in Procs : i \notin suspected[i]

(* Liveness properties *)

\* Every crashed process is eventually permanently suspected by every
\* correct process.
StrongCompleteness ==
    \A i, j \in Procs :
        <>[]((~alive[i] /\ alive[j]) => i \in suspected[j])

\* Eventually, no correct process is suspected by any correct process.
EventuallyStrongAccuracy ==
    \A i, j \in Procs :
        <>[]((alive[i] /\ alive[j]) => i \notin suspected[j])

THEOREM Spec => [](TypeOK /\ PartialSynchrony /\ CrashBound /\ NoSelfSuspicion)
THEOREM Spec => StrongCompleteness /\ EventuallyStrongAccuracy
=============================================================================