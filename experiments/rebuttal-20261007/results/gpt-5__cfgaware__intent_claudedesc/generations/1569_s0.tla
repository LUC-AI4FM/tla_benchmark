---- MODULE Bakery ----
EXTENDS Naturals

CONSTANTS
  NumProcs, \* Number of processes
  MaxNum    \* Maximum ticket value (bound)

ProcSet == 1..NumProcs

VARIABLES
  pc,        \* program counter per process: "Idle","Read","WaitInit","Wait","CS"
  choosing,  \* choosing flag per process
  num,       \* ticket number per process, bounded by MaxNum
  maxSeen,   \* per-process running maximum observed during choosing
  readSet,   \* per-process set of processes left to read during choosing
  waitSet    \* per-process set of processes left to check during waiting

vars == << pc, choosing, num, maxSeen, readSet, waitSet >>

Others(i) == ProcSet \ {i}

Lt(i, j) == num[i] < num[j] \/ (num[i] = num[j] /\ i < j)

Init ==
  /\ pc = [ i \in ProcSet |-> "Idle" ]
  /\ choosing = [ i \in ProcSet |-> FALSE ]
  /\ num = [ i \in ProcSet |-> 0 ]
  /\ maxSeen = [ i \in ProcSet |-> 0 ]
  /\ readSet = [ i \in ProcSet |-> {} ]
  /\ waitSet = [ i \in ProcSet |-> {} ]

ChooseStart(i) ==
  /\ pc[i] = "Idle"
  /\ pc' = [pc EXCEPT ![i] = "Read"]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ maxSeen' = [maxSeen EXCEPT ![i] = 0]
  /\ readSet' = [readSet EXCEPT ![i] = Others(i)]
  /\ UNCHANGED << num, waitSet >>

ReadOne(i) ==
  /\ pc[i] = "Read"
  /\ \E j \in readSet[i]:
       /\ ~choosing[j]
       /\ maxSeen' = [maxSeen EXCEPT ![i] = IF maxSeen[i] >= num[j] THEN maxSeen[i] ELSE num[j]]
       /\ readSet' = [readSet EXCEPT ![i] = readSet[i] \ {j}]
  /\ UNCHANGED << pc, choosing, num, waitSet >>

AssignTicket(i) ==
  /\ pc[i] = "Read"
  /\ readSet[i] = {}
  /\ pc' = [pc EXCEPT ![i] = "WaitInit"]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ num' = [num EXCEPT ![i] = IF maxSeen[i] + 1 <= MaxNum THEN maxSeen[i] + 1 ELSE MaxNum]
  /\ UNCHANGED << maxSeen, readSet, waitSet >>

WaitInit(i) ==
  /\ pc[i] = "WaitInit"
  /\ waitSet' = [waitSet EXCEPT ![i] = Others(i)]
  /\ pc' = [pc EXCEPT ![i] = "Wait"]
  /\ UNCHANGED << choosing, num, maxSeen, readSet >>

WaitOne(i) ==
  /\ pc[i] = "Wait"
  /\ \E j \in waitSet[i]:
       /\ ~choosing[j]
       /\ (num[j] = 0 \/ Lt(i, j))
       /\ waitSet' = [waitSet EXCEPT ![i] = waitSet[i] \ {j}]
  /\ UNCHANGED << pc, choosing, num, maxSeen, readSet >>

EnterCS(i) ==
  /\ pc[i] = "Wait"
  /\ waitSet[i] = {}
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << choosing, num, maxSeen, readSet, waitSet >>

LeaveCS(i) ==
  /\ pc[i] = "CS"
  /\ pc' = [pc EXCEPT ![i] = "Idle"]
  /\ num' = [num EXCEPT ![i] = 0]
  /\ UNCHANGED << choosing, maxSeen, readSet, waitSet >>

ProcAction(i) ==
  ChooseStart(i)
  \/ ReadOne(i)
  \/ AssignTicket(i)
  \/ WaitInit(i)
  \/ WaitOne(i)
  \/ EnterCS(i)
  \/ LeaveCS(i)

Next ==
  \E i \in ProcSet : ProcAction(i)

Spec ==
  Init /\ [][Next]_vars

Invariant ==
  \A i, j \in ProcSet : i # j => ~(pc[i] = "CS" /\ pc[j] = "CS")

====