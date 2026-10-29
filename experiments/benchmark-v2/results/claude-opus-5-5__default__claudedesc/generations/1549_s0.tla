------------------------------- MODULE EventuallyPerfectFailureDetector -------------------------------
(***************************************************************************)
(* An eventually perfect failure detector (<>P) in a partially synchronous *)
(* system (Chandra and Toueg, 1996).  The specification composes:         *)
(*   - Age_Channel       : message transport with message ages            *)
(*   - EPFailureDetector : behavior of correct processes                  *)
(* within an environment controller that governs global time, crashes and  *)
(* the partial-synchrony bounds DELTA (message delay) and PHI (relative    *)
(* process speed).                                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,             \* number of processes
          T,             \* maximum number of failures
          d0,            \* default timeout
          SendPoint,     \* local clock period for sending "alive" messages
          PredictPoint,  \* local clock period for updating suspicions
          DELTA,         \* bound on message delay
          PHI            \* bound on relative process speed

ASSUME /\ N \in Nat \ {0}
       /\ T \in Nat /\ T < N
       /\ d0 \in Nat
       /\ SendPoint \in Nat \ {0}
       /\ PredictPoint \in Nat \ {0}
       /\ DELTA \in Nat
       /\ PHI \in Nat

Procs == 1..N

Msg == [from : Procs, to : Procs, content : {"alive"}, age : Nat]

ClockPeriod == SendPoint * PredictPoint

VARIABLES inTransit,       \* messages in transit (Age_Channel)
          inDelivery,      \* messages ready to be delivered (Age_Channel)
          suspected,       \* suspected[i] : processes suspected by i
          delta,           \* delta[i][j]  : timeout of i for j
          fromLastHeard,   \* fromLastHeard[i][j] : local ticks since i heard from j
          localClock,      \* local clock of each process
          outgoingMessages,\* messages last sent by each process
          procPause,       \* global ticks since a process last moved
          moved,           \* last action of each process in current tick
          failed,          \* crash flags
          F                \* number of crashed processes

chanVars == <<inTransit, inDelivery>>
fdVars   == <<suspected, delta, fromLastHeard, localClock, outgoingMessages>>
envVars  == <<procPause, moved, failed, F>>
vars     == <<inTransit, inDelivery, suspected, delta, fromLastHeard,
              localClock, outgoingMessages, procPause, moved, failed, F>>

Actions == {"tick", "send", "predict", "receive", "crash"}

---------------------------------------------------------------------------
TypeOK ==
  /\ inTransit \subseteq Msg
  /\ inDelivery \subseteq Msg
  /\ suspected \in [Procs -> SUBSET Procs]
  /\ delta \in [Procs -> [Procs -> Nat]]
  /\ fromLastHeard \in [Procs -> [Procs -> Nat]]
  /\ localClock \in [Procs -> Nat]
  /\ outgoingMessages \in [Procs -> SUBSET Msg]
  /\ procPause \in [Procs -> Nat]
  /\ moved \in [Procs -> Actions]
  /\ failed \in [Procs -> BOOLEAN]
  /\ F \in 0..T

Init ==
  /\ inTransit = {}
  /\ inDelivery = {}
  /\ suspected = [i \in Procs |-> {}]
  /\ delta = [i \in Procs |-> [j \in Procs |-> d0]]
  /\ fromLastHeard = [i \in Procs |-> [j \in Procs |-> 0]]
  /\ localClock = [i \in Procs |-> 0]
  /\ outgoingMessages = [i \in Procs |-> {}]
  /\ procPause = [i \in Procs |-> 0]
  /\ moved = [i \in Procs |-> "tick"]
  /\ failed = [i \in Procs |-> FALSE]
  /\ F = 0

---------------------------------------------------------------------------
(* Age_Channel helpers *)
Age(S) == {[m EXCEPT !.age = m.age + 1] : m \in S}

(* EPFailureDetector helpers *)
IncHeard(i, j) ==
  IF fromLastHeard[i][j] > delta[i][j]
    THEN fromLastHeard[i][j]
    ELSE fromLastHeard[i][j] + 1

NextClock(i) == (localClock[i] + 1) % ClockPeriod

IsSendTime(i)    == localClock[i] % SendPoint = 0
IsPredictTime(i) == ~IsSendTime(i) /\ localClock[i] % PredictPoint = 0
IsReceiveTime(i) == ~IsSendTime(i) /\ ~IsPredictTime(i)

Send(i) ==
  LET msgs == {[from |-> i, to |-> j, content |-> "alive", age |-> 0] :
                 j \in Procs \ {i}}
  IN /\ IsSendTime(i)
     /\ outgoingMessages' = [outgoingMessages EXCEPT ![i] = msgs]
     /\ inTransit' = inTransit \cup msgs
     /\ fromLastHeard' = [fromLastHeard EXCEPT ![i] =
                            [j \in Procs |-> IncHeard(i, j)]]
     /\ localClock' = [localClock EXCEPT ![i] = NextClock(i)]
     /\ moved' = [moved EXCEPT ![i] = "send"]
     /\ UNCHANGED <<inDelivery, suspected, delta>>

Predict(i) ==
  /\ IsPredictTime(i)
  /\ suspected' = [suspected EXCEPT ![i] =
                     suspected[i] \cup
                       {j \in Procs \ {i} : fromLastHeard[i][j] > delta[i][j]}]
  /\ fromLastHeard' = [fromLastHeard EXCEPT ![i] =
                         [j \in Procs |-> IncHeard(i, j)]]
  /\ localClock' = [localClock EXCEPT ![i] = NextClock(i)]
  /\ moved' = [moved EXCEPT ![i] = "predict"]
  /\ UNCHANGED <<inTransit, inDelivery, delta, outgoingMessages>>

Receive(i) ==
  LET rcv     == {m \in inDelivery : m.to = i}
      senders == {m.from : m \in rcv}
  IN /\ IsReceiveTime(i)
     /\ inDelivery' = inDelivery \ rcv
     /\ delta' = [delta EXCEPT ![i] =
                    [j \in Procs |->
                       IF j \in senders /\ j \in suspected[i]
                         THEN delta[i][j] + 1
                         ELSE delta[i][j]]]
     /\ suspected' = [suspected EXCEPT ![i] = suspected[i] \ senders]
     /\ fromLastHeard' = [fromLastHeard EXCEPT ![i] =
                            [j \in Procs |->
                               IF j \in senders THEN 0 ELSE IncHeard(i, j)]]
     /\ localClock' = [localClock EXCEPT ![i] = NextClock(i)]
     /\ moved' = [moved EXCEPT ![i] = "receive"]
     /\ UNCHANGED <<inTransit, outgoingMessages>>

(* Messages addressed to a crashed process are drained by the channel *)
Drain(i) ==
  /\ failed[i]
  /\ \E m \in inTransit \cup inDelivery : m.to = i
  /\ inTransit' = {m \in inTransit : m.to # i}
  /\ inDelivery' = {m \in inDelivery : m.to # i}
  /\ UNCHANGED <<fdVars, envVars>>

---------------------------------------------------------------------------
(* Environment actions *)

Crash(i) ==
  /\ ~failed[i]
  /\ F < T
  /\ failed' = [failed EXCEPT ![i] = TRUE]
  /\ F' = F + 1
  /\ moved' = [moved EXCEPT ![i] = "crash"]
  /\ UNCHANGED <<chanVars, fdVars, procPause>>

EnvTick ==
  /\ \E i \in Procs : ~failed[i] /\ moved[i] # "tick"
  /\ \E S \in SUBSET inTransit :
        /\ inTransit' = Age(inTransit \ S)
        /\ inDelivery' = Age(inDelivery \cup S)
  /\ procPause' = [i \in Procs |->
                     IF failed[i] THEN procPause[i] ELSE procPause[i] + 1]
  /\ moved' = [i \in Procs |-> IF failed[i] THEN moved[i] ELSE "tick"]
  /\ UNCHANGED <<fdVars, failed, F>>

ProcTick(i) ==
  \/ /\ ~failed[i]
     /\ moved[i] = "tick"
     /\ procPause' = [procPause EXCEPT ![i] = 0]
     /\ UNCHANGED <<failed, F>>
     /\ \/ Send(i)
        \/ Predict(i)
        \/ Receive(i)
  \/ Drain(i)

---------------------------------------------------------------------------
(* Partial-synchrony constraints *)
DELTAConstraint == \A m \in inTransit \cup inDelivery : m.age <= DELTA

PHIConstraint == \A i \in Procs : ~failed[i] => procPause[i] <= PHI

Constraints == DELTAConstraint' /\ PHIConstraint'

CrashC       == (\E i \in Procs : Crash(i)) /\ Constraints
EnvTickC     == EnvTick /\ Constraints
ProcTickC(i) == ProcTick(i) /\ Constraints

Next ==
  \/ CrashC
  \/ EnvTickC
  \/ \E i \in Procs : ProcTickC(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(EnvTickC)
  /\ \A i \in Procs : WF_vars(ProcTickC(i))

---------------------------------------------------------------------------
(* Properties of <>P *)

(* Every crashed process is eventually permanently suspected by every     *)
(* correct process.                                                        *)
StrongCompleteness ==
  <>[](\A i, j \in Procs :
          (~failed[i] /\ failed[j]) => j \in suspected[i])

(* There is a time after which no correct process is suspected by any     *)
(* correct process.                                                        *)
EventuallyStrongAccuracy ==
  <>[](\A i, j \in Procs :
          (~failed[i] /\ ~failed[j]) => j \notin suspected[i])

THEOREM Spec => []TypeOK
THEOREM Spec => StrongCompleteness /\ EventuallyStrongAccuracy
=============================================================================