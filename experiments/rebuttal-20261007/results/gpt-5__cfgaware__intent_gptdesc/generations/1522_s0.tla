------------------------------ MODULE HuangTermination ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Proc,          \* set of processes
  Leader,        \* designated coordinator, an element of Proc
  DenomBound     \* positive natural giving the fixed denominator (total weight)

\* Variables
VARIABLES
  status,   \* [Proc -> {"active","idle"}]
  w,        \* [Proc -> 0..DenomBound], local integer weights summing (with msgs) to DenomBound
  msgs,     \* Seq(Message), multiset of in-transit messages (arbitrary reordering)
  detected  \* BOOLEAN, becomes TRUE when leader detects termination

\* Message records carry weight from a sender to a receiver.
Message == [src: Proc, dst: Proc, wt: 1..DenomBound]

\* Helper: remove the i-th element from a sequence (1-based).
RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

\* Derived predicates
AllIdle == \A p \in Proc: status[p] = "idle"
GloballyQuiescent == AllIdle /\ Len(msgs) = 0
TerminationDetected == detected

\* Initial state
Init ==
  /\ Leader \in Proc
  /\ DenomBound \in Nat \ {0}
  /\ status = [p \in Proc |-> IF p = Leader THEN "active" ELSE "idle"]
  /\ w = [p \in Proc |-> IF p = Leader THEN DenomBound ELSE 0]
  /\ msgs = << >>
  /\ detected = FALSE

\* Actions

\* Active process p sends a positive weight a to q (q != p), reducing its local weight.
Send(p, q, a) ==
  /\ ~detected
  /\ p \in Proc /\ q \in Proc /\ p # q
  /\ status[p] = "active"
  /\ a \in 1..w[p]
  /\ status' = status
  /\ w' = [w EXCEPT ![p] = @ - a]
  /\ msgs' = msgs \o << [src |-> p, dst |-> q, wt |-> a] >>
  /\ detected' = detected

\* Deliver any one in-transit message, adding its weight to the destination and
\* making the destination active.
Receive(i) ==
  /\ ~detected
  /\ i \in 1..Len(msgs)
  /\ LET m == msgs[i]
     IN /\ msgs' = RemoveAt(msgs, i)
        /\ w' = [w EXCEPT ![m.dst] = @ + m.wt]
        /\ status' = [status EXCEPT ![m.dst] = "active"]
        /\ detected' = detected

\* An active process becomes idle.
\* - If p = Leader: it simply becomes idle (keeps its weight).
\* - If p != Leader: it sends all its current weight back to the Leader and zeroes its local weight.
BecomeIdle(p) ==
  /\ ~detected
  /\ p \in Proc
  /\ status[p] = "active"
  /\ IF p = Leader
        THEN /\ status' = [status EXCEPT ![p] = "idle"]
             /\ w' = w
             /\ msgs' = msgs
        ELSE /\ status' = [status EXCEPT ![p] = "idle"]
             /\ w' = [w EXCEPT ![p] = 0]
             /\ msgs' = IF w[p] = 0
                        THEN msgs
                        ELSE msgs \o << [src |-> p, dst |-> Leader, wt |-> w[p]] >>
  /\ detected' = detected

\* Any idle process may (spontaneously) become active without changing weights.
Activate(p) ==
  /\ ~detected
  /\ p \in Proc
  /\ status[p] = "idle"
  /\ status' = [status EXCEPT ![p] = "active"]
  /\ w' = w
  /\ msgs' = msgs
  /\ detected' = detected

\* The leader declares (detects) termination when idle and it has accumulated all weight,
\* with no messages in transit.
Detect ==
  /\ ~detected
  /\ status[Leader] = "idle"
  /\ w[Leader] = DenomBound
  /\ Len(msgs) = 0
  /\ detected' = TRUE
  /\ status' = status
  /\ w' = w
  /\ msgs' = msgs

\* Next-state relation: arbitrary interleaving of process actions and message deliveries.
Next ==
  \/ \E p \in Proc, q \in Proc, a \in 1..DenomBound: a <= w[p] /\ p # q /\ Send(p, q, a)
  \/ \E i \in 1..Len(msgs): Receive(i)
  \/ \E p \in Proc: BecomeIdle(p)
  \/ \E p \in Proc: Activate(p)
  \/ Detect

vars == << status, w, msgs, detected >>

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Detect)

\* Finite-sum helpers for invariants

RECURSIVE ProcSum(_)
ProcSum(S) ==
  IF S = {} THEN 0
  ELSE LET p == CHOOSE q \in S: TRUE
       IN w[p] + ProcSum(S \ {p})

RECURSIVE MsgSum(_)
MsgSum(n) ==
  IF n = 0 THEN 0
  ELSE msgs[n].wt + MsgSum(n-1)

TotalWeight == ProcSum(Proc) + MsgSum(Len(msgs))

\* Invariants and properties

\* Type correctness and basic assumptions
TypeInv ==
  /\ Leader \in Proc
  /\ DenomBound \in Nat \ {0}
  /\ IsFiniteSet(Proc)
  /\ status \in [Proc -> {"active", "idle"}]
  /\ w \in [Proc -> 0..DenomBound]
  /\ msgs \in Seq(Message)
  /\ detected \in BOOLEAN

\* Conservation of total weight (always equals DenomBound).
WeightConservation == (TotalWeight = DenomBound)

\* Safety: once termination is detected, thereafter all processes remain idle and no messages exist.
Safety == [](detected => GloballyQuiescent)

\* Liveness: whenever the system becomes globally quiescent, eventually the leader detects termination.
Liveness == [](GloballyQuiescent => <> TerminationDetected)

\* Practical state constraint preventing Zeno behaviors:
\* All weights are integer multiples of 1/DenomBound; messages carry positive integer quanta.
StateConstraint ==
  /\ DenomBound \in Nat \ {0}
  /\ \A p \in Proc: w[p] \in 0..DenomBound
  /\ \A i \in 1..Len(msgs): msgs[i].wt \in 1..DenomBound

=============================================================================