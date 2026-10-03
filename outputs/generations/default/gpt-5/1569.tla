----------------------------- MODULE Bakery -----------------------------
EXTENDS Naturals, TLC

CONSTANT N, MaxTicket

ASSUME N \in Nat /\ N >= 1 /\ MaxTicket \in Nat

Proc == 1..N

VARIABLES
  pc,            \* control locations per process
  choosing,      \* [Proc -> BOOLEAN]
  number,        \* [Proc -> Nat]
  j,             \* next process index examined per process, in 1..(N+1)
  readNum,       \* per-process local read set of ticket numbers: [Proc -> [Proc -> Nat]]
  readChoosing,  \* per-process local read set of choosing flags: [Proc -> [Proc -> BOOLEAN]]
  maxNum         \* per-process local maximum observed ticket number

Vars == << pc, choosing, number, j, readNum, readChoosing, maxNum >>

MaxOf(S) == IF S = {} THEN 0 ELSE CHOOSE m \in S : \A n \in S : n <= m

TypeOK ==
  /\ pc \in [Proc -> {"start","choose","chooseDone","waitChoosing","waitNumber","cs","exit"}]
  /\ choosing \in [Proc -> BOOLEAN]
  /\ number \in [Proc -> Nat]
  /\ j \in [Proc -> (1..(N+1))]
  /\ readNum \in [Proc -> [Proc -> Nat]]
  /\ readChoosing \in [Proc -> [Proc -> BOOLEAN]]
  /\ maxNum \in [Proc -> Nat]

Init ==
  /\ pc = [i \in Proc |-> "start"]
  /\ choosing = [i \in Proc |-> FALSE]
  /\ number = [i \in Proc |-> 0]
  /\ j = [i \in Proc |-> 1]
  /\ readNum = [i \in Proc |-> [k \in Proc |-> 0]]
  /\ readChoosing = [i \in Proc |-> [k \in Proc |-> FALSE]]
  /\ maxNum = [i \in Proc |-> 0]

Start(self) ==
  /\ self \in Proc
  /\ pc[self] = "start"
  /\ choosing' = [choosing EXCEPT ![self] = TRUE]
  /\ pc' = [pc EXCEPT ![self] = "choose"]
  /\ UNCHANGED << number, j, readNum, readChoosing, maxNum >>

Choose(self) ==
  /\ self \in Proc
  /\ pc[self] = "choose"
  /\ LET m == MaxOf({ number[k] : k \in Proc })
     IN
       /\ maxNum' = [maxNum EXCEPT ![self] = m]
       /\ number' = [number EXCEPT ![self] = m + 1]
  /\ readNum' = [readNum EXCEPT ![self] = [k \in Proc |-> number[k]]]
  /\ pc' = [pc EXCEPT ![self] = "chooseDone"]
  /\ UNCHANGED << choosing, j, readChoosing >>

ChooseDone(self) ==
  /\ self \in Proc
  /\ pc[self] = "chooseDone"
  /\ choosing' = [choosing EXCEPT ![self] = FALSE]
  /\ j' = [j EXCEPT ![self] = 1]
  /\ pc' = [pc EXCEPT ![self] = "waitChoosing"]
  /\ UNCHANGED << number, readNum, readChoosing, maxNum >>

WaitChoosingAdvance(self) ==
  /\ self \in Proc
  /\ pc[self] = "waitChoosing"
  /\ j[self] <= N
  /\ (j[self] = self \/ choosing[j[self]] = FALSE)
  /\ readChoosing' =
       [readChoosing EXCEPT
         ![self] = [readChoosing[self] EXCEPT ![j[self]] = choosing[j[self]]]]
  /\ j' = [j EXCEPT ![self] = j[self] + 1]
  /\ pc' = pc
  /\ UNCHANGED << choosing, number, readNum, maxNum >>

WaitChoosingDone(self) ==
  /\ self \in Proc
  /\ pc[self] = "waitChoosing"
  /\ j[self] = N + 1
  /\ j' = [j EXCEPT ![self] = 1]
  /\ pc' = [pc EXCEPT ![self] = "waitNumber"]
  /\ UNCHANGED << choosing, number, readNum, readChoosing, maxNum >>

WaitNumberAdvance(self) ==
  /\ self \in Proc
  /\ pc[self] = "waitNumber"
  /\ j[self] <= N
  /\ ( j[self] = self
     \/ number[j[self]] = 0
     \/ number[j[self]] > number[self]
     \/ (number[j[self]] = number[self] /\ j[self] > self) )
  /\ readNum' =
       [readNum EXCEPT
         ![self] = [readNum[self] EXCEPT ![j[self]] = number[j[self]]]]
  /\ j' = [j EXCEPT ![self] = j[self] + 1]
  /\ pc' = pc
  /\ UNCHANGED << choosing, number, readChoosing, maxNum >>

WaitNumberDone(self) ==
  /\ self \in Proc
  /\ pc[self] = "waitNumber"
  /\ j[self] = N + 1
  /\ j' = [j EXCEPT ![self] = 1]
  /\ pc' = [pc EXCEPT ![self] = "cs"]
  /\ UNCHANGED << choosing, number, readNum, readChoosing, maxNum >>

CS(self) ==
  /\ self \in Proc
  /\ pc[self] = "cs"
  /\ pc' = [pc EXCEPT ![self] = "exit"]
  /\ UNCHANGED << choosing, number, j, readNum, readChoosing, maxNum >>

Exit(self) ==
  /\ self \in Proc
  /\ pc[self] = "exit"
  /\ number' = [number EXCEPT ![self] = 0]
  /\ pc' = [pc EXCEPT ![self] = "start"]
  /\ UNCHANGED << choosing, j, readNum, readChoosing, maxNum >>

Next ==
  \E self \in Proc:
      Start(self)
    \/ Choose(self)
    \/ ChooseDone(self)
    \/ WaitChoosingAdvance(self)
    \/ WaitChoosingDone(self)
    \/ WaitNumberAdvance(self)
    \/ WaitNumberDone(self)
    \/ CS(self)
    \/ Exit(self)

Spec == Init /\ [][Next]_Vars

MutualExclusion ==
  Cardinality({ i \in Proc : pc[i] = "cs" }) <= 1

TicketBound == \A i \in Proc : number[i] <= MaxTicket
StateConstraint == TicketBound
===========================================================================