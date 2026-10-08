----------------------------- MODULE Bakery -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, TicketBound

ASSUME /\ N \in Nat \ {0}
       /\ TicketBound \in Nat \ {0}

(*
  Process set and ticket type
*)
Proc == 1..N
Ticket == 0..TicketBound

(*
  State variables
  - choosing[i] indicates process i is in the ticket-choosing phase
  - number[i] is the ticket number of process i (0 means not contending)
  - pc[i] is the control state of process i
  - idx[i] is the current index being scanned by process i during waiting
*)
VARIABLES choosing, number, pc, idx

vars == << choosing, number, pc, idx >>

(*
  Helper: maximum of a finite set of natural numbers
*)
MaxNat(S) == IF S = {} THEN 0
             ELSE CHOOSE m \in S : \A n \in S : m >= n

MaxNumber == MaxNat({ number[k] : k \in Proc })

(*
  Lexicographic priority: j has priority over i iff
  number[j] < number[i] \/ (number[j] = number[i] /\ j < i)
*)
Priority(j, i) == (number[j] < number[i])
                  \/ (number[j] = number[i] /\ j < i)

(*
  Initialization: nobody contends, all idle
*)
Init ==
  /\ choosing = [i \in Proc |-> FALSE]
  /\ number   = [i \in Proc |-> 0]
  /\ pc       = [i \in Proc |-> "idle"]
  /\ idx      = [i \in Proc |-> 1]

(*
  Process i actions
*)
StartChoose(i) ==
  /\ pc[i] = "idle"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ pc'       = [pc EXCEPT ![i] = "choose1"]
  /\ UNCHANGED << number, idx >>

PickNumber(i) ==
  /\ pc[i] = "choose1"
  /\ MaxNumber + 1 <= TicketBound
  /\ number' = [number EXCEPT ![i] = MaxNumber + 1]
  /\ pc'     = [pc EXCEPT ![i] = "choose2"]
  /\ UNCHANGED << choosing, idx >>

FinishChoose(i) ==
  /\ pc[i] = "choose2"
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ idx'      = [idx EXCEPT ![i] = 1]
  /\ pc'       = [pc EXCEPT ![i] = "waitCh"]
  /\ UNCHANGED number

(*
  Wait until every j has choosing[j] = FALSE, scanning sequentially by idx[i]
*)
WaitChAdvance(i) ==
  /\ pc[i] = "waitCh"
  /\ idx[i] <= N
  /\ ( idx[i] = i \/ ~choosing[idx[i]] )
  /\ idx' = [idx EXCEPT ![i] = idx[i] + 1]
  /\ UNCHANGED << choosing, number, pc >>

WaitChDone(i) ==
  /\ pc[i] = "waitCh"
  /\ idx[i] = N + 1
  /\ idx' = [idx EXCEPT ![i] = 1]
  /\ pc'  = [pc EXCEPT ![i] = "waitOr"]
  /\ UNCHANGED << choosing, number >>

(*
  Wait until for every j:
    number[j] = 0 \/ not Priority(j,i),
  again scanning sequentially by idx[i]
*)
WaitOrAdvance(i) ==
  /\ pc[i] = "waitOr"
  /\ idx[i] <= N
  /\ ( idx[i] = i
       \/ LET j == idx[i] IN (number[j] = 0 \/ ~Priority(j,i)) )
  /\ idx' = [idx EXCEPT ![i] = idx[i] + 1]
  /\ UNCHANGED << choosing, number, pc >>

WaitOrDone(i) ==
  /\ pc[i] = "waitOr"
  /\ idx[i] = N + 1
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << choosing, number, idx >>

ExitCS(i) ==
  /\ pc[i] = "cs"
  /\ number' = [number EXCEPT ![i] = 0]
  /\ pc'     = [pc EXCEPT ![i] = "idle"]
  /\ idx'    = [idx EXCEPT ![i] = 1]
  /\ UNCHANGED choosing

Proc(i) ==
  StartChoose(i)
  \/ PickNumber(i)
  \/ FinishChoose(i)
  \/ WaitChAdvance(i)
  \/ WaitChDone(i)
  \/ WaitOrAdvance(i)
  \/ WaitOrDone(i)
  \/ ExitCS(i)

Next == \E i \in Proc : Proc(i)

(*
  Fairness: weak fairness for each process's step
*)
Spec == Init /\ [][Next]_vars /\ (\A i \in Proc : WF_vars(Proc(i)))

(*
  Typing and structural invariants
*)
TypeOK ==
  /\ choosing \in [Proc -> BOOLEAN]
  /\ number   \in [Proc -> Ticket]
  /\ pc       \in [Proc -> {"idle","choose1","choose2","waitCh","waitOr","cs"}]
  /\ idx      \in [Proc -> 1..(N+1)]

NumberBoundInv == \A i \in Proc : number[i] \in Ticket

(*
  Mutual exclusion: at most one process in the critical section
*)
CS == { i \in Proc : pc[i] = "cs" }
MutualExclusion == Cardinality(CS) <= 1

(*
  Ordering invariant: if i is in CS, then no j has strict priority over i
  (i.e., no j with a smaller ticket, or same ticket and smaller id) while contending.
*)
OrderInvariant ==
  \A i, j \in Proc :
    i # j /\ pc[i] = "cs" /\ number[j] # 0
      => ~Priority(j, i)

(*
  Scan progress invariants to aid verification/inspection
*)
WaitChScanInv ==
  \A i \in Proc :
    pc[i] = "waitCh" =>
      \A j \in Proc \ {i} : j < idx[i] => ~choosing[j]

WaitOrScanInv ==
  \A i \in Proc :
    pc[i] = "waitOr" =>
      \A j \in Proc \ {i} : j < idx[i] => ~(number[j] # 0 /\ Priority(j,i))

(*
  Trying predicate and deadlock-absence condition when someone is trying
*)
PreCS == {"choose1","choose2","waitCh","waitOr"}
Trying(i) == pc[i] \in PreCS
SomeTrying == \E i \in Proc : Trying(i)
EnabledNext == ENABLED Next
NoDeadlockWhenTrying == [] (SomeTrying => EnabledNext)

(*
  Liveness properties (to be checked under the fairness in Spec)
  - Starvation freedom per attempt: once a process is trying, it will eventually enter CS.
  - After entering CS, it eventually resets its ticket to 0 (exit action does this immediately).
*)
StarvationFree ==
  \A i \in Proc : (pc[i] \in PreCS) ~> (pc[i] = "cs")

EventuallyReset ==
  \A i \in Proc : [] (pc[i] = "cs" => <> (number[i] = 0))
=============================================================================