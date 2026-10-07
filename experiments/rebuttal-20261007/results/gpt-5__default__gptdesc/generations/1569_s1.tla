------------------------------ MODULE Bakery ------------------------------

EXTENDS Naturals, TLC, FiniteSets

CONSTANTS Proc, MaxTicket

ASSUME Proc \subseteq Nat /\ Proc # {} /\ MaxTicket \in Nat

VARIABLES
  pc,            \* control locations per process
  choosing,      \* [Proc -> BOOLEAN]
  number,        \* [Proc -> Nat]
  mx,            \* per-process cached max ticket computed before entering
  next,          \* per-process next process examined (nondeterministic choice)
  readNum,       \* per-process local read cache of number
  readChoosing   \* per-process local read cache of choosing

vars == << pc, choosing, number, mx, next, readNum, readChoosing >>

PcLabels == {"start", "choose1", "choose2", "wait", "cs", "exit"}

TypeOK ==
  /\ pc \in [Proc -> PcLabels]
  /\ choosing \in [Proc -> BOOLEAN]
  /\ number \in [Proc -> Nat]
  /\ mx \in [Proc -> Nat]
  /\ next \in [Proc -> Proc]
  /\ readNum \in [Proc -> [Proc -> Nat]]
  /\ readChoosing \in [Proc -> [Proc -> BOOLEAN]]

Init ==
  /\ pc = [i \in Proc |-> "start"]
  /\ choosing = [i \in Proc |-> FALSE]
  /\ number = [i \in Proc |-> 0]
  /\ mx = [i \in Proc |-> 0]
  /\ next = [i \in Proc |-> CHOOSE j \in Proc : TRUE]
  /\ readNum = [i \in Proc |-> [j \in Proc |-> 0]]
  /\ readChoosing = [i \in Proc |-> [j \in Proc |-> FALSE]]
  /\ TypeOK

Less(i, j) ==
  number[i] < number[j]
  \/ (number[i] = number[j] /\ i < j)

Eligible(i) ==
  \A j \in Proc \ {i} :
    ~choosing[j] /\ (number[j] = 0 \/ Less(i, j))

Start(i) ==
  /\ pc[i] = "start"
  /\ pc' = [pc EXCEPT ![i] = "choose1"]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED << number, mx, next, readNum, readChoosing >>

Choose1(i) ==
  /\ pc[i] = "choose1"
  /\ LET m == 1 + Max({ number[j] : j \in Proc }) IN
     /\ mx' = [mx EXCEPT ![i] = m]
     /\ number' = [number EXCEPT ![i] = m]
  /\ pc' = [pc EXCEPT ![i] = "choose2"]
  /\ UNCHANGED << choosing, next, readNum, readChoosing >>

Choose2(i) ==
  /\ pc[i] = "choose2"
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ next' = [next EXCEPT ![i] = CHOOSE j \in Proc : TRUE]
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED << number, mx, readNum, readChoosing >>

WaitGotoCS(i) ==
  /\ pc[i] = "wait"
  /\ Eligible(i)
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << choosing, number, mx, next, readNum, readChoosing >>

WaitSpin(i) ==
  /\ pc[i] = "wait"
  /\ ~Eligible(i)
  /\ readChoosing' =
       [readChoosing EXCEPT
          ![i] = [readChoosing[i] EXCEPT ![next[i]] = choosing[next[i]]]]
  /\ readNum' =
       [readNum EXCEPT
          ![i] = [readNum[i] EXCEPT ![next[i]] = number[next[i]]]]
  /\ next' = [next EXCEPT ![i] = CHOOSE j \in Proc : TRUE]
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED << choosing, number, mx >>

CS(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << choosing, number, mx, next, readNum, readChoosing >>

Exit(i) ==
  /\ pc[i] = "exit"
  /\ number' = [number EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "start"]
  /\ UNCHANGED << choosing, mx, next, readNum, readChoosing >>

ProcStep(i) ==
  Start(i) \/ Choose1(i) \/ Choose2(i) \/ WaitGotoCS(i) \/ WaitSpin(i) \/ CS(i) \/ Exit(i)

Next ==
  \E i \in Proc : ProcStep(i)

Spec ==
  Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in Proc : \A q \in Proc :
    p # q => ~(pc[p] = "cs" /\ pc[q] = "cs")

TicketBound ==
  \A i \in Proc : number[i] <= MaxTicket

Inv ==
  TypeOK /\ MutualExclusion

=============================================================================