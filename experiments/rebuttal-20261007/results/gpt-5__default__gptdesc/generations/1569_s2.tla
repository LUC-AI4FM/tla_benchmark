--------------------------- MODULE Bakery ---------------------------

EXTENDS Naturals

CONSTANTS
  Proc,          \* Nonempty set of process ids, assumed subset of Nat
  TicketBound    \* Natural number used to bound ticket values for TLC

ASSUME /\ Proc # {}
       /\ Proc \subseteq Nat
       /\ TicketBound \in Nat

VARIABLES
  pc,             \* control location per process
  choosing,       \* [Proc -> BOOLEAN]
  number,         \* [Proc -> Nat], bounded by TicketBound via state constraint
  max,            \* per-process local maximum seen while choosing a ticket
  read,           \* per-process local set of processes already read when computing max
  waitChooseSet,  \* per-process local set of processes to wait for choosing[j] = FALSE
  waitNumSet      \* per-process local set of processes to wait for ticket order condition

vars == << pc, choosing, number, max, read, waitChooseSet, waitNumSet >>

LexLess(i, j) ==
  /\ number[i] < number[j]
  \/ /\ number[i] = number[j]
     /\ i < j

Init ==
  /\ pc \in [Proc -> {"start"}]
  /\ choosing = [i \in Proc |-> FALSE]
  /\ number   = [i \in Proc |-> 0]
  /\ max      = [i \in Proc |-> 0]
  /\ read     = [i \in Proc |-> {}]
  /\ waitChooseSet = [i \in Proc |-> {}]
  /\ waitNumSet    = [i \in Proc |-> {}]

Start(i) ==
  /\ pc[i] = "start"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ max'      = [max EXCEPT ![i] = 0]
  /\ read'     = [read EXCEPT ![i] = {}]
  /\ pc'       = [pc EXCEPT ![i] = "scan"]
  /\ UNCHANGED << number, waitChooseSet, waitNumSet >>

ScanProgress(i) ==
  /\ pc[i] = "scan"
  /\ \E k \in Proc \ read[i]:
        /\ max'  = [max EXCEPT ![i] = IF max[i] >= number[k] THEN max[i] ELSE number[k]]
        /\ read' = [read EXCEPT ![i] = read[i] \cup {k}]
        /\ UNCHANGED << choosing, number, waitChooseSet, waitNumSet, pc >>

ScanDone(i) ==
  /\ pc[i] = "scan"
  /\ read[i] = Proc
  /\ number'        = [number EXCEPT ![i] = max[i] + 1]
  /\ choosing'      = [choosing EXCEPT ![i] = FALSE]
  /\ waitChooseSet' = [waitChooseSet EXCEPT ![i] = Proc \ {i}]
  /\ pc'            = [pc EXCEPT ![i] = "wait1"]
  /\ UNCHANGED << max, read, waitNumSet >>

WaitChooseRemove(i) ==
  /\ pc[i] = "wait1"
  /\ \E j \in waitChooseSet[i]:
        /\ ~choosing[j]
        /\ waitChooseSet' = [waitChooseSet EXCEPT ![i] = waitChooseSet[i] \ {j}]
        /\ UNCHANGED << choosing, number, read, max, waitNumSet, pc >>

WaitChooseDone(i) ==
  /\ pc[i] = "wait1"
  /\ waitChooseSet[i] = {}
  /\ waitNumSet' = [waitNumSet EXCEPT ![i] = Proc \ {i}]
  /\ pc'         = [pc EXCEPT ![i] = "wait2"]
  /\ UNCHANGED << choosing, number, read, max, waitChooseSet >>

WaitNumRemove(i) ==
  /\ pc[i] = "wait2"
  /\ \E j \in waitNumSet[i]:
        /\ (number[j] = 0) \/ LexLess(i, j)
        /\ waitNumSet' = [waitNumSet EXCEPT ![i] = waitNumSet[i] \ {j}]
        /\ UNCHANGED << choosing, number, read, max, waitChooseSet, pc >>

WaitNumDone(i) ==
  /\ pc[i] = "wait2"
  /\ waitNumSet[i] = {}
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << choosing, number, read, max, waitChooseSet, waitNumSet >>

CSExit(i) ==
  /\ pc[i] = "cs"
  /\ number' = [number EXCEPT ![i] = 0]
  /\ pc'     = [pc EXCEPT ![i] = "start"]
  /\ UNCHANGED << choosing, read, max, waitChooseSet, waitNumSet >>

ProcStep(i) ==
  \/ Start(i)
  \/ ScanProgress(i)
  \/ ScanDone(i)
  \/ WaitChooseRemove(i)
  \/ WaitChooseDone(i)
  \/ WaitNumRemove(i)
  \/ WaitNumDone(i)
  \/ CSExit(i)

Next ==
  \E i \in Proc : ProcStep(i)

Spec ==
  Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

TicketBoundConstraint ==
  \A i \in Proc : number[i] <= TicketBound

INVARIANT MutualExclusion

CONSTRAINT TicketBoundConstraint

==========================================================================