----------------------------- MODULE HuangWeightedTermination -----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Proc,        \* Finite set of processes
  Leader,      \* The distinguished coordinator/leader
  QTotal       \* Total weight quanta (a positive natural), represents weight 1 as QTotal units

ASSUME Leader \in Proc
ASSUME QTotal \in Nat \ {0}
ASSUME IsFiniteSet(Proc)

VARIABLES
  active,       \* subset of Proc: currently active processes
  localWeight,  \* function [Proc -> Nat]: local weight held by each process (in quanta)
  msgs,         \* set of in-transit messages; each message is a record [id, from, to, w]
  nextId,       \* next message id (Nat), grows monotonically
  detected      \* Bool: leader has detected termination

\* Message shape and helper predicates/operators

IsMsg(m) ==
  /\ m \in [id: Nat, from: Proc, to: Proc, w: Nat]
  /\ m.w \in 1..QTotal

UniqueIds(M) ==
  \A m1, m2 \in M: m1 # m2 => m1.id # m2.id

RECURSIVE SumFun(_, _)
SumFun(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S: TRUE IN
      f[x] + SumFun(f, S \ {x})

RECURSIVE SumMsgSet(_)
SumMsgSet(M) ==
  IF M = {} THEN 0
  ELSE
    LET m == CHOOSE m \in M: TRUE IN
      m.w + SumMsgSet(M \ {m})

AllIdle == active = {}
MessagesEmpty == msgs = {}

TotalLocal == SumFun(localWeight, Proc)
TotalMsgs  == SumMsgSet(msgs)

\* Safety: Conservation of total weight (locals + in-transit) equals QTotal at all times.
Conservation == TotalLocal + TotalMsgs = QTotal

\* Practical state constraint (anti-Zeno): integral quanta bounded by QTotal.
NoZeno ==
  /\ \A p \in Proc: localWeight[p] \in 0..QTotal
  /\ \A m \in msgs: m.w \in 1..QTotal

\* Non-leader processes cannot hold weight while idle.
IdleZeroNonLeader ==
  \A p \in Proc: (p # Leader /\ p \notin active) => localWeight[p] = 0

TypeInv ==
  /\ active \subseteq Proc
  /\ localWeight \in [Proc -> Nat]
  /\ \A p \in Proc: localWeight[p] <= QTotal
  /\ \A m \in msgs: IsMsg(m)
  /\ UniqueIds(msgs)
  /\ \A m \in msgs: m.id < nextId
  /\ nextId \in Nat
  /\ detected \in BOOLEAN

Inv == TypeInv /\ Conservation /\ NoZeno /\ IdleZeroNonLeader

Init ==
  /\ active = {Leader}
  /\ localWeight = [p \in Proc |-> IF p = Leader THEN QTotal ELSE 0]
  /\ msgs = {}
  /\ nextId = 0
  /\ detected = FALSE

\* Actions

Send(p, q, w) ==
  /\ p \in active
  /\ q \in Proc
  /\ w \in 1..localWeight[p]
  /\ msgs' = msgs \cup { [id |-> nextId, from |-> p, to |-> q, w |-> w] }
  /\ localWeight' = [localWeight EXCEPT ![p] = @ - w]
  /\ nextId' = nextId + 1
  /\ active' = active
  /\ detected' = detected

Receive(q, m) ==
  /\ m \in msgs
  /\ q = m.to
  /\ msgs' = msgs \ { m }
  /\ localWeight' = [localWeight EXCEPT ![q] = @ + m.w]
  /\ active' = active \cup { q }
  /\ nextId' = nextId
  /\ detected' = detected

IdleReturn(p) ==
  /\ p \in active
  /\ LET w == localWeight[p] IN
       /\ active' = active \ { p }
       /\ localWeight' = [localWeight EXCEPT ![p] = 0]
       /\ IF p # Leader /\ w > 0
            THEN /\ msgs' = msgs \cup { [id |-> nextId, from |-> p, to |-> Leader, w |-> w] }
                 /\ nextId' = nextId + 1
            ELSE /\ msgs' = msgs
                 /\ nextId' = nextId
  /\ detected' = detected

\* Leader declares termination only when the system is globally quiescent and it holds all weight.
DetectTerm ==
  /\ ~detected
  /\ AllIdle
  /\ MessagesEmpty
  /\ localWeight[Leader] = QTotal
  /\ detected' = TRUE
  /\ UNCHANGED << active, localWeight, msgs, nextId >>

\* After detection, the system does not evolve further (termination).
TerminatedStutter ==
  /\ detected
  /\ UNCHANGED << active, localWeight, msgs, nextId, detected >>

Next ==
  \/ DetectTerm
  \/ IF detected
        THEN TerminatedStutter
        ELSE
          \/ \E p \in active, q \in Proc, w \in 1..localWeight[p]: Send(p, q, w)
          \/ \E m \in msgs: Receive(m.to, m)
          \/ \E p \in active: IdleReturn(p)

vars == << active, localWeight, msgs, nextId, detected >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(DetectTerm)

\* Stated safety and liveness requirements:

\* Safety: once detected, thereafter all processes are idle and no messages are in transit.
Safety ==
  [](detected => (AllIdle /\ MessagesEmpty))

\* Liveness: whenever the system globally quiesces, eventually the leader detects termination.
Liveness ==
  []((AllIdle /\ MessagesEmpty) => <>detected)

\* Invariant bundle (state safety, including conservation and anti-Zeno constraint):
ConservationInv == []Conservation
StateConstraints == [] (TypeInv /\ NoZeno /\ IdleZeroNonLeader)

==========================================================================================