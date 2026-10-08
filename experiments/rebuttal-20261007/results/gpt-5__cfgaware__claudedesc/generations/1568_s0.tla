------------------------------ MODULE Bakery ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  NumProcs,
  MaxNum

Proc == 1..NumProcs

(*
  Program counter labels:
    "loop" : start of picking a ticket
    "d1"   : scanning all tickets to compute max
    "d2"   : computing next ticket number (max + 1)
    "d3"   : publishing ticket and clearing choosing flag
    "w1"   : waiting until each other process finishes choosing
    "w2"   : waiting for lexicographic order condition
    "cs"   : critical section
*)

VARIABLES
  pc,        \* [Proc -> {"loop","d1","d2","d3","w1","w2","cs"}]
  choosing,  \* [Proc -> BOOLEAN]
  num,       \* [Proc -> Nat] (ticket numbers; 0 means no ticket)
  read,      \* [Proc -> Nat] (current index being scanned; ranges over Proc and may be NumProcs+1)
  max,       \* [Proc -> Nat] (max ticket seen while scanning)
  nxt        \* [Proc -> Nat] (candidate ticket = max + 1)

vars == << pc, choosing, num, read, max, nxt >>

Init ==
  /\ pc = [ i \in Proc |-> "loop" ]
  /\ choosing = [ i \in Proc |-> FALSE ]
  /\ num = [ i \in Proc |-> 0 ]
  /\ read = [ i \in Proc |-> 1 ]
  /\ max = [ i \in Proc |-> 0 ]
  /\ nxt = [ i \in Proc |-> 0 ]

Loop(i) ==
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ read' = [read EXCEPT ![i] = 1]
  /\ max' = [max EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "d1"]
  /\ UNCHANGED << num, nxt >>

D1(i) ==
  \/ /\ read[i] <= NumProcs
     /\ LET r == read[i] IN
        /\ max' =
             [max EXCEPT ![i] =
               IF num[r] > max[i] THEN num[r] ELSE max[i]]
        /\ read' = [read EXCEPT ![i] = r + 1]
        /\ pc' = [pc EXCEPT ![i] = "d1"]
        /\ UNCHANGED << choosing, num, nxt >>
  \/ /\ read[i] = NumProcs + 1
     /\ pc' = [pc EXCEPT ![i] = "d2"]
     /\ UNCHANGED << choosing, num, read, max, nxt >>

D2(i) ==
  /\ nxt' = [nxt EXCEPT ![i] = max[i] + 1]
  /\ pc' = [pc EXCEPT ![i] = "d3"]
  /\ UNCHANGED << choosing, num, read, max >>

D3(i) ==
  /\ num' = [num EXCEPT ![i] = nxt[i]]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ read' = [read EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ UNCHANGED << max, nxt >>

W1(i) ==
  \/ /\ read[i] > NumProcs
     /\ pc' = [pc EXCEPT ![i] = "cs"]
     /\ UNCHANGED << choosing, num, read, max, nxt >>
  \/ /\ read[i] <= NumProcs /\ read[i] = i
     /\ read' = [read EXCEPT ![i] = read[i] + 1]
     /\ pc' = [pc EXCEPT ![i] = "w1"]
     /\ UNCHANGED << choosing, num, max, nxt >>
  \/ /\ read[i] <= NumProcs /\ read[i] # i /\ ~choosing[read[i]]
     /\ pc' = [pc EXCEPT ![i] = "w2"]
     /\ UNCHANGED << choosing, num, read, max, nxt >>

W2(i) ==
  /\ read[i] <= NumProcs /\ read[i] # i
  /\ ( num[read[i]] = 0
     \/ num[read[i]] > num[i]
     \/ (num[read[i]] = num[i] /\ read[i] > i)
     )
  /\ read' = [read EXCEPT ![i] = read[i] + 1]
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ UNCHANGED << choosing, num, max, nxt >>

CS(i) ==
  /\ num' = [num EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "loop"]
  /\ UNCHANGED << choosing, read, max, nxt >>

ProcStep(i) ==
  \/ pc[i] = "loop" /\ Loop(i)
  \/ pc[i] = "d1"   /\ D1(i)
  \/ pc[i] = "d2"   /\ D2(i)
  \/ pc[i] = "d3"   /\ D3(i)
  \/ pc[i] = "w1"   /\ W1(i)
  \/ pc[i] = "w2"   /\ W2(i)
  \/ pc[i] = "cs"   /\ CS(i)

Next ==
  \E i \in Proc : ProcStep(i)

Spec ==
  Init /\ [][Next]_vars

(*
  Safety invariant: mutual exclusion — at most one process in "cs".
*)
Invariant ==
  \A i, j \in Proc : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

(*
  Optional helpers often used in configurations:
  - Constraint: state constraint to bound ticket-related values
  - InCS: count of processes currently in the critical section
*)
Constraint ==
  /\ \A i \in Proc : num[i] \in 0..MaxNum
  /\ \A i \in Proc : max[i] \in 0..MaxNum
  /\ \A i \in Proc : nxt[i] \in 0..MaxNum

InCS ==
  Cardinality({ i \in Proc : pc[i] = "cs" })

=============================================================================