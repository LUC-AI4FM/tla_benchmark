----------------------------- MODULE HuangTermination -----------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Procs, \* Non-empty finite set of process identifiers
  Leader, \* Distinguished initiator/leader in Procs
  Units    \* The total initial weight, modeled as a positive integer "power-of-two" mass

ASSUME Leader \in Procs
Pow2 == { n \in Nat : \E k \in Nat : n = 2^k }
ASSUME Units \in Pow2

VARIABLES
  active,       \* [Procs -> BOOLEAN], whether a process is active
  weight,       \* [Procs -> Nat], the local weight (integer units)
  chan,         \* Seq of messages in transit; each message has fields [src, dst, units]
  detectedTerm  \* BOOLEAN, whether the leader has detected global termination

Vars == << active, weight, chan, detectedTerm >>

Message == [src: Procs, dst: Procs, units: Nat]

TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ weight \in [Procs -> Nat]
  /\ chan \in Seq(Message)
  /\ \A i \in 1..Len(chan) : chan[i].units > 0
  /\ detectedTerm \in BOOLEAN

Init ==
  /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]
  /\ weight = [p \in Procs |-> IF p = Leader THEN Units ELSE 0]
  /\ chan = << >>
  /\ detectedTerm = FALSE

\* Remove the i-th element (1-based) from a sequence
RemoveAt(s, i) ==
  [ j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1] ]

RECURSIVE SeqUnitsSum(_)
SeqUnitsSum(s) ==
  IF Len(s) = 0
  THEN 0
  ELSE s[1].units + SeqUnitsSum(Tail(s))

RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {}
  THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

TotalLocalWeight == Sum(weight, Procs)
TotalInTransit  == SeqUnitsSum(chan)

Conservation == TotalLocalWeight + TotalInTransit = Units

\* Action: process p sends a message to q, transferring exactly half of its local weight
Send(p, q) ==
  /\ p \in Procs
  /\ q \in Procs
  /\ p # q
  /\ active[p]
  /\ weight[p] \geq 2
  /\ LET u == weight[p] \div 2
     IN /\ u \geq 1
        /\ chan' = Append(chan, [src |-> p, dst |-> q, units |-> u])
        /\ weight' = [weight EXCEPT ![p] = weight[p] - u]
        /\ UNCHANGED << active, detectedTerm >>

SendAny == \E p \in Procs : \E q \in Procs \ {p} : Send(p, q)

\* Action: deliver any in-transit message (ensures progress under fairness)
Receive(i) ==
  /\ i \in 1..Len(chan)
  /\ LET m == chan[i]
     IN /\ chan' = RemoveAt(chan, i)
        /\ weight' = [weight EXCEPT ![m.dst] = weight[m.dst] + m.units]
        /\ active' = [active EXCEPT ![m.dst] = TRUE]
        /\ UNCHANGED detectedTerm

ReceiveAny == \E i \in 1..Len(chan) : Receive(i)

\* Action: a process becomes idle (application-level quiescence)
Idle(p) ==
  /\ p \in Procs
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ UNCHANGED << weight, chan, detectedTerm >>

IdleAny == \E p \in Procs : Idle(p)

\* Action: the leader detects termination when idle, holding all weight, and no messages remain
Detect ==
  /\ ~detectedTerm
  /\ ~active[Leader]
  /\ Len(chan) = 0
  /\ weight[Leader] = Units
  /\ detectedTerm' = TRUE
  /\ UNCHANGED << active, weight, chan >>

Next == SendAny \/ ReceiveAny \/ IdleAny \/ Detect

Spec ==
  Init /\ [][Next]_Vars
  /\ WF_Vars(ReceiveAny)   \* fairness: messages are eventually delivered
  /\ WF_Vars(IdleAny)      \* fairness: an enabled idle transition eventually occurs
  /\ WF_Vars(Detect)       \* fairness: detection occurs when its condition holds

\* Safety invariants
SafetyTypeOK           == []TypeOK
SafetyConservation     == []Conservation
AllIdleAndEmpty        == (\A p \in Procs : ~active[p]) /\ Len(chan) = 0
SafetyDetectSoundness  == [](detectedTerm => AllIdleAndEmpty)

\* Liveness: eventually, termination is detected
TerminationEventuallyDetected == <>detectedTerm

\* Optional liveness strengthening: if the system becomes quiescent, detection follows
TerminationImpliesDetection == [](AllIdleAndEmpty => <>detectedTerm)

=============================================================================