----------------------------- MODULE Bakery -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, TicketBound

ASSUME /\ N \in Nat \ {0}
       /\ TicketBound \in Nat

Proc == 1..N

VARIABLES pc, choosing, number, j, maxNum, readN, readC

PCStates ==
  {"ncs","choose1","choose2","choose3","wait1","wait2","wait3","cs","release"}

vars == << pc, choosing, number, j, maxNum, readN, readC >>

TypeOK ==
  /\ pc \in [Proc -> PCStates]
  /\ choosing \in [Proc -> BOOLEAN]
  /\ number \in [Proc -> Nat]
  /\ j \in [Proc -> 1..(N+1)]
  /\ maxNum \in [Proc -> Nat]
  /\ readN \in [Proc -> SUBSET Proc]
  /\ readC \in [Proc -> SUBSET Proc]

Init ==
  /\ pc = [i \in Proc |-> "ncs"]
  /\ choosing = [i \in Proc |-> FALSE]
  /\ number = [i \in Proc |-> 0]
  /\ j = [i \in Proc |-> 1]
  /\ maxNum = [i \in Proc |-> 0]
  /\ readN = [i \in Proc |-> {}]
  /\ readC = [i \in Proc |-> {}]
  /\ TypeOK

PairLess(m,i,n,k) == (m < n) \/ (m = n /\ i < k)

NonCrit(i) ==
  /\ i \in Proc
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "choose1"]
  /\ UNCHANGED << choosing, number, j, maxNum, readN, readC >>

Choose1(i) ==
  /\ i \in Proc
  /\ pc[i] = "choose1"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ readN' = [readN EXCEPT ![i] = {}]
  /\ readC' = [readC EXCEPT ![i] = {}]
  /\ pc' = [pc EXCEPT ![i] = "choose2"]
  /\ UNCHANGED << number, j, maxNum >>

Choose2(i) ==
  /\ i \in Proc
  /\ pc[i] = "choose2"
  /\ LET m == Max({ number[k] : k \in Proc })
     IN /\ number' = [number EXCEPT ![i] = m + 1]
        /\ maxNum' = [maxNum EXCEPT ![i] = m]
  /\ readN' = [readN EXCEPT ![i] = Proc]
  /\ pc' = [pc EXCEPT ![i] = "choose3"]
  /\ UNCHANGED << choosing, j, readC >>

Choose3(i) ==
  /\ i \in Proc
  /\ pc[i] = "choose3"
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = "wait1"]
  /\ UNCHANGED << number, maxNum, readN, readC >>

WaitSkipSelf(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait1"
  /\ j[i] <= N
  /\ j[i] = i
  /\ j' = [j EXCEPT ![i] = j[i] + 1]
  /\ UNCHANGED << pc, choosing, number, maxNum, readN, readC >>

WaitGoCheck(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait1"
  /\ j[i] <= N
  /\ j[i] # i
  /\ pc' = [pc EXCEPT ![i] = "wait2"]
  /\ UNCHANGED << choosing, number, j, maxNum, readN, readC >>

AwaitChoose(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait2"
  /\ j[i] <= N
  /\ ~choosing[j[i]]
  /\ readC' = [readC EXCEPT ![i] = readC[i] \cup { j[i] }]
  /\ pc' = [pc EXCEPT ![i] = "wait3"]
  /\ UNCHANGED << choosing, number, j, maxNum, readN >>

AwaitNumber(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait3"
  /\ j[i] <= N
  /\ LET ji == j[i] IN
     /\ ( number[ji] = 0
        \/ number[ji] > number[i]
        \/ (number[ji] = number[i] /\ ji >= i)
        )
     /\ readN' = [readN EXCEPT ![i] = readN[i] \cup { ji }]
     /\ LET newJ == ji + 1 IN
        /\ j' = [j EXCEPT ![i] = newJ]
        /\ pc' = [pc EXCEPT ![i] = IF newJ > N THEN "cs" ELSE "wait1"]
  /\ UNCHANGED << choosing, number, maxNum, readC >>

EnterCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "release"]
  /\ UNCHANGED << choosing, number, j, maxNum, readN, readC >>

Release(i) ==
  /\ i \in Proc
  /\ pc[i] = "release"
  /\ number' = [number EXCEPT ![i] = 0]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ maxNum' = [maxNum EXCEPT ![i] = 0]
  /\ readN' = [readN EXCEPT ![i] = {}]
  /\ readC' = [readC EXCEPT ![i] = {}]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED choosing

ProcStep(i) ==
  NonCrit(i)
  \/ Choose1(i)
  \/ Choose2(i)
  \/ Choose3(i)
  \/ WaitSkipSelf(i)
  \/ WaitGoCheck(i)
  \/ AwaitChoose(i)
  \/ AwaitNumber(i)
  \/ EnterCS(i)
  \/ Release(i)

Next ==
  \E i \in Proc: ProcStep(i)

Fairness ==
  \A i \in Proc: WF_vars(ProcStep(i))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
  Cardinality({ i \in Proc: pc[i] = "cs" }) <= 1

StateConstraint ==
  \A i \in Proc: number[i] <= TicketBound
============================================================================