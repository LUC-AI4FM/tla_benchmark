------------------------------- MODULE Bakery -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcs, MaxNum

Proc == 1..NumProcs

VARIABLES
  choosing,   \* [Proc -> BOOLEAN]
  number,     \* [Proc -> Nat]
  pc,         \* [Proc -> STRING], control locations
  seen,       \* [Proc -> SUBSET Proc], per-process read set while computing max
  maxv,       \* [Proc -> Nat], per-process running maximum of ticket numbers
  nxt         \* [Proc -> Nat], per-process next process examined

vars == << choosing, number, pc, seen, maxv, nxt >>

Init ==
  /\ choosing = [i \in Proc |-> FALSE]
  /\ number   = [i \in Proc |-> 0]
  /\ pc       = [i \in Proc |-> "start"]
  /\ seen     = [i \in Proc |-> {}]
  /\ maxv     = [i \in Proc |-> 0]
  /\ nxt      = [i \in Proc |-> 1]

\* Lexicographic order on tickets: (n,i) < (m,j)
TicketLess(i, j) ==
  \/ number[i] < number[j]
  \/ (number[i] = number[j] /\ i < j)

WaitOk(i, j) ==
  \/ j = i
  \/ (~choosing[j] /\ (number[j] = 0 \/ TicketLess(i, j)))

Start(i) ==
  /\ i \in Proc
  /\ pc[i] = "start"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ seen'     = [seen     EXCEPT ![i] = {}]
  /\ maxv'     = [maxv     EXCEPT ![i] = 0]
  /\ nxt'      = [nxt      EXCEPT ![i] = 1]
  /\ pc'       = [pc       EXCEPT ![i] = "scanMax"]
  /\ UNCHANGED number

ScanMaxStep(i) ==
  /\ i \in Proc
  /\ pc[i] = "scanMax"
  /\ nxt[i] <= NumProcs
  /\ LET j == nxt[i] IN
       /\ maxv' = [maxv EXCEPT ![i] = IF number[j] > maxv[i] THEN number[j] ELSE maxv[i]]
       /\ seen' = [seen EXCEPT ![i] = seen[i] \cup {j}]
       /\ nxt'  = [nxt  EXCEPT ![i] = nxt[i] + 1]
       /\ pc' = pc
       /\ UNCHANGED << choosing, number >>

FinishChoose(i) ==
  /\ i \in Proc
  /\ pc[i] = "scanMax"
  /\ nxt[i] > NumProcs
  /\ number'   = [number   EXCEPT ![i] = maxv[i] + 1]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ nxt'      = [nxt      EXCEPT ![i] = 1]
  /\ pc'       = [pc       EXCEPT ![i] = "wait"]
  /\ UNCHANGED << seen, maxv >>

WaitPass(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait"
  /\ nxt[i] <= NumProcs
  /\ LET j == nxt[i] IN
       /\ WaitOk(i, j)
       /\ nxt' = [nxt EXCEPT ![i] = nxt[i] + 1]
       /\ pc' = pc
       /\ UNCHANGED << choosing, number, seen, maxv >>

EnterCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait"
  /\ nxt[i] > NumProcs
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << choosing, number, seen, maxv, nxt >>

LeaveCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ number' = [number EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "start"]
  /\ UNCHANGED << choosing, seen, maxv, nxt >>

Next ==
  \E i \in Proc :
       Start(i)
    \/ ScanMaxStep(i)
    \/ FinishChoose(i)
    \/ WaitPass(i)
    \/ EnterCS(i)
    \/ LeaveCS(i)

Spec == Init /\ [][Next]_vars

InCS == { i \in Proc : pc[i] = "cs" }
Invariant == Cardinality(InCS) <= 1

\* Optional TLC state constraint bounding ticket values
StateConstraint ==
  /\ \A i \in Proc : number[i] <= MaxNum
  /\ \A i \in Proc : maxv[i]   <= MaxNum

=============================================================================