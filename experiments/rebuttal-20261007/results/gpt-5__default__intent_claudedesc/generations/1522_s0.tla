---------------------------- MODULE HuangTermination ----------------------------

EXTENDS Naturals, FiniteSets, Sequences, Reals

(*
  Constants:
    - Proc: finite nonempty set of processes
    - Leader: designated leader in Proc
*)
CONSTANTS Proc, Leader

ASSUME Leader \in Proc

(*
  Helper sets and operators
*)
NonLeaders == Proc \ {Leader}
Pairs == Proc \X Proc

RECURSIVE Sum(_,_)
Sum(S, f) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S: TRUE
       IN f[x] + Sum(S \ {x}, f)

Fst(t) == t[1]
Snd(t) == t[2]

(*
  State variables
    - active[p] \in BOOLEAN: whether process p is active
    - w[p] \in Reals: local weight of process p
    - reg[p][q] \in Reals: total weight in-flight as regular messages from p to q
    - ret[p] \in Reals for p \in NonLeaders: total weight in-flight as return-to-leader from p
*)
VARIABLES active, w, reg, ret

vars == << active, w, reg, ret >>

(*
  Derived state predicates and measures
*)
LocalSum ==
  Sum(Proc, [p \in Proc |-> w[p]])

RegSum ==
  Sum(Pairs, [t \in Pairs |-> reg[Fst(t)][Snd(t)]])

ReturnSum ==
  SumNonLeaders == Sum(NonLeaders, [p \in NonLeaders |-> ret[p]])

TotalWeight == LocalSum + RegSum + ReturnSum

NoRegMsgs == \A p \in Proc: \A q \in Proc: reg[p][q] = 0
NoRetMsgs == \A p \in NonLeaders: ret[p] = 0
NoMsgs == NoRegMsgs /\ NoRetMsgs

AllIdle == \A p \in Proc: ~active[p]

Detect == ~active[Leader] /\ w[Leader] = 1

(*
  Initialization
    - Only leader is active with weight 1
    - Others are idle with weight 0
    - No messages in transit
*)
Init ==
  /\ active = [p \in Proc |-> IF p = Leader THEN TRUE ELSE FALSE]
  /\ w = [p \in Proc |-> IF p = Leader THEN 1 ELSE 0]
  /\ reg = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ ret = [p \in NonLeaders |-> 0]

(*
  Actions
*)

Send(p, q) ==
  /\ p \in Proc /\ q \in Proc /\ p # q
  /\ active[p]
  /\ w[p] > 0
  /\ LET half == w[p] / 2 IN
       /\ w' = [w EXCEPT ![p] = w[p] - half]
       /\ reg' = [reg EXCEPT ![p][q] = reg[p][q] + half]
       /\ UNCHANGED << active, ret >>

ReceiveReg(r, s) ==
  /\ r \in Proc /\ s \in Proc
  /\ reg[s][r] > 0
  /\ LET amt == reg[s][r] IN
       /\ w' = [w EXCEPT ![r] = w[r] + amt]
       /\ reg' = [reg EXCEPT ![s][r] = 0]
       /\ active' = [active EXCEPT ![r] = TRUE]
       /\ UNCHANGED ret

ReceiveReturn(p) ==
  /\ p \in NonLeaders
  /\ ret[p] > 0
  /\ LET amt == ret[p] IN
       /\ w' = [w EXCEPT ![Leader] = w[Leader] + amt]
       /\ ret' = [ret EXCEPT ![p] = 0]
       /\ active' = [active EXCEPT ![Leader] = TRUE]
       /\ UNCHANGED reg

IdleNonLeader(p) ==
  /\ p \in NonLeaders
  /\ active[p]
  /\ ret' = [ret EXCEPT ![p] = ret[p] + w[p]]
  /\ w' = [w EXCEPT ![p] = 0]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ UNCHANGED reg

IdleLeader ==
  /\ active[Leader]
  /\ active' = [active EXCEPT ![Leader] = FALSE]
  /\ UNCHANGED << w, reg, ret >>

Next ==
  \/ \E p \in Proc: \E q \in Proc \ {p}: Send(p, q)
  \/ \E r \in Proc: \E s \in Proc: ReceiveReg(r, s)
  \/ \E p \in NonLeaders: ReceiveReturn(p)
  \/ \E p \in NonLeaders: IdleNonLeader(p)
  \/ IdleLeader

(*
  Fairness assumptions:
    - Weak fairness on receiving of any in-flight message (both regular and return),
      ensuring messages are eventually delivered if continuously enabled.
*)
Fairness ==
  /\ \A r \in Proc: \A s \in Proc: WF_vars(ReceiveReg(r, s))
  /\ \A p \in NonLeaders: WF_vars(ReceiveReturn(p))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

(*
  Safety invariants
    - Weight is conserved and nonnegative
    - No false detection: if leader is idle with full weight, then system is genuinely
      quiescent (all idle, no messages), and this condition is stable once reached.
*)
NonNegativity ==
  /\ \A p \in Proc: w[p] >= 0
  /\ \A t \in Pairs: reg[Fst(t)][Snd(t)] >= 0
  /\ \A p \in NonLeaders: ret[p] >= 0

WeightConservation == TotalWeight = 1

NoFalseDetectionAlways == [](Detect => (AllIdle /\ NoMsgs))

Stability ==
  [](Detect => [](Detect /\ AllIdle /\ NoMsgs))

AlwaysSafety ==
  [] (WeightConservation /\ NonNegativity) /\ NoFalseDetectionAlways /\ Stability

(*
  Liveness property:
    If the system genuinely terminates (eventually remains with all processes idle
    and no messages in transit), then the leader eventually detects termination.
*)
Terminated == AllIdle /\ NoMsgs

TerminationLiveness ==
  (<>[] Terminated) => <> Detect

===============================================================================