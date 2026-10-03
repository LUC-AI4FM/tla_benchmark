------------------------------ MODULE HuangTermination ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  Huang's distributed termination detection algorithm (simplified, model-checkable).
  - Processes split weight with computation messages by halving (on even weights).
  - Messages carry dyadic rational weights with denominator 2^K (modeled as integers 0..Denom).
  - The sum of all process weights and in-transit message weights is always Denom (represents 1).
  - Non-leader idle processes eventually return all of their weight to the Leader via a control message.
  - The Leader detects termination when it is idle, all are idle, all queues are empty, and it holds weight Denom.
*)

CONSTANTS
  Procs,    \* nonempty finite set of processes
  Leader,   \* a distinguished process in Procs
  K         \* natural, denominator exponent so total weight = 2^K

(*
  Basic numeric helpers
*)
RECURSIVE TwoTo(_)
TwoTo(n) == IF n = 0 THEN 1 ELSE 2 * TwoTo(n - 1)

Denom == TwoTo(K)

(*
  Message structure and queues
*)
MessageSet == [from: Procs, to: Procs, w: 0..Denom]

(*
  State variables
*)
VARIABLES
  active,    \* [Procs -> BOOLEAN]
  weight,    \* [Procs -> 0..Denom]
  inbox,     \* [Procs -> Seq(MessageSet)]
  detected   \* BOOLEAN

vars == << active, weight, inbox, detected >>

(*
  Type correctness and helper sums
*)
TypeOK ==
  /\ K \in Nat
  /\ Leader \in Procs
  /\ Procs # {} /\ IsFiniteSet(Procs)
  /\ active \in [Procs -> BOOLEAN]
  /\ weight \in [Procs -> 0..Denom]
  /\ inbox \in [Procs -> Seq(MessageSet)]
  /\ detected \in BOOLEAN
  /\ \A p \in Procs: \A m \in Seq(MessageSet): TRUE   \* sanity; sequences over MessageSet

RECURSIVE ProcSum(_)
ProcSum(S) ==
  IF S = {} THEN 0
  ELSE
    LET p == CHOOSE x \in S: TRUE IN
      weight[p] + ProcSum(S \ {p})

RECURSIVE SumMsgSeq(_)
SumMsgSeq(s) ==
  IF Len(s) = 0 THEN 0
  ELSE s[1].w + SumMsgSeq(Tail(s))

RECURSIVE MsgSumOverProcs(_)
MsgSumOverProcs(S) ==
  IF S = {} THEN 0
  ELSE
    LET p == CHOOSE x \in S: TRUE IN
      SumMsgSeq(inbox[p]) + MsgSumOverProcs(S \ {p})

TotalWeight == ProcSum(Procs) + MsgSumOverProcs(Procs)

WeightInv == TotalWeight = Denom

(*
  Derived state predicates
*)
NoMsgs == \A p \in Procs: Len(inbox[p]) = 0
AllIdle == \A p \in Procs: ~active[p]
Detected == detected

(*
  Initialization
*)
Init ==
  /\ TypeOK
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN Denom ELSE 0]
  /\ inbox = [p \in Procs |-> << >>]
  /\ detected = FALSE
  /\ WeightInv

(*
  Queue helpers
*)
Head(s) == s[1]
TailOrEmpty(s) == IF Len(s) = 0 THEN << >> ELSE Tail(s)

Enqueue(q, m) == q \o << m >>

(*
  Actions
  All non-stuttering actions are disabled once detected = TRUE.
*)

(*
  A process p sends a computation message to q by halving its current even weight.
*)
Send(p, q) ==
  /\ ~detected
  /\ p \in Procs /\ q \in Procs
  /\ active[p] = TRUE
  /\ weight[p] \in 0..Denom
  /\ weight[p] >= 2
  /\ weight[p] % 2 = 0
  LET half == weight[p] \div 2 IN
    /\ weight' = [weight EXCEPT ![p] = @ - half]
    /\ inbox' = [inbox EXCEPT ![q] = Enqueue(@, [from |-> p, to |-> q, w |-> half])]
    /\ active' = active
    /\ detected' = detected

(*
  A process q receives the head of its inbox, adding the carried weight and becoming active.
*)
Receive(q) ==
  /\ ~detected
  /\ q \in Procs
  /\ Len(inbox[q]) > 0
  LET m == Head(inbox[q]) IN
    /\ inbox' = [inbox EXCEPT ![q] = Tail(inbox[q])]
    /\ weight' = [weight EXCEPT ![q] = @ + m.w]
    /\ active' = [active EXCEPT ![q] = TRUE]
    /\ detected' = detected

(*
  A process p may become idle at any time when active.
*)
Idle(p) ==
  /\ ~detected
  /\ p \in Procs
  /\ active[p] = TRUE
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ weight' = weight
  /\ inbox' = inbox
  /\ detected' = detected

(*
  An idle non-leader process returns all of its current weight to the Leader via a control message.
*)
ReturnToLeader(p) ==
  /\ ~detected
  /\ p \in Procs \ {Leader}
  /\ active[p] = FALSE
  /\ weight[p] > 0
  /\ inbox' = [inbox EXCEPT ![Leader] = Enqueue(@, [from |-> p, to |-> Leader, w |-> weight[p]])]
  /\ weight' = [weight EXCEPT ![p] = 0]
  /\ active' = active
  /\ detected' = detected

(*
  The leader detects termination when everyone is idle, there are no messages,
  and it holds all the weight.
*)
Detect ==
  /\ ~detected
  /\ AllIdle
  /\ NoMsgs
  /\ weight[Leader] = Denom
  /\ detected' = TRUE
  /\ active' = active
  /\ weight' = weight
  /\ inbox' = inbox

(*
  Stuttering when detected is TRUE (system quiescent after detection)
*)
QuiescentStutter ==
  /\ detected
  /\ UNCHANGED vars

SendAny    == \E p \in Procs: \E q \in Procs: Send(p, q)
ReceiveAny == \E p \in Procs: Receive(p)
IdleAny    == \E p \in Procs: Idle(p)
ReturnAny  == \E p \in Procs: ReturnToLeader(p)

Next ==
  SendAny
  \/ ReceiveAny
  \/ IdleAny
  \/ ReturnAny
  \/ Detect
  \/ QuiescentStutter

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ReceiveAny)
  /\ WF_vars(ReturnAny)
  /\ WF_vars(IdleAny)
  /\ WF_vars(Detect)

(*
  Properties
*)
Safety ==
  [](Detected => (AllIdle /\ NoMsgs))

Liveness ==
  <>Detected

=============================================================================