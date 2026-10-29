---------------------------- MODULE Bakery ----------------------------
(***************************************************************************)
(* Lamport's Bakery algorithm for NumProcs processes and one critical      *)
(* section. Reads and writes of shared registers are atomic, and          *)
(* processes interleave arbitrarily.                                       *)
(*                                                                         *)
(* Each process cycles through these steps:                                *)
(*   ncs  : noncritical section. The process may stay here forever.       *)
(*   e1   : choosing := TRUE; start scanning the others' tickets.          *)
(*   e2   : scan loop. Read num[j] for one unchecked j and track the max. *)
(*   e3   : take ticket num[self] := max + 1.                              *)
(*   e4   : choosing := FALSE; prepare the wait loop.                      *)
(*   w1   : pick an unchecked process nxt and wait until ~flag[nxt].       *)
(*   w2   : wait until num[nxt] = 0 or <<num[self],self>> << <<num[nxt],nxt>>.*)
(*   cs   : critical section.                                              *)
(*   exit : release the ticket, num[self] := 0.                            *)
(*                                                                         *)
(* Ticket values are unbounded in the algorithm. For model checking, the  *)
(* state constraint Constraint bounds them by MaxNum.                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcs, MaxNum

ASSUME NumProcsAssump == NumProcs \in Nat \ {0}
ASSUME MaxNumAssump   == MaxNum \in Nat \ {0}

Procs == 1..NumProcs

(* Lexicographic order on <<ticket, process id>> pairs, used to break ties *)
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1] /\ a[2] < b[2])

VARIABLES
  num,        \* num[i]       : ticket of process i (0 = not contending)
  flag,       \* flag[i]      : "choosing" flag of process i
  pc,         \* pc[i]        : control location of process i
  unchecked,  \* unchecked[i] : processes not yet scanned or checked by i
  max,        \* max[i]       : largest ticket i has seen while scanning
  nxt         \* nxt[i]       : process i is currently waiting on

vars == <<num, flag, pc, unchecked, max, nxt>>

Labels == {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}

-----------------------------------------------------------------------------
Init == /\ num       = [i \in Procs |-> 0]
        /\ flag      = [i \in Procs |-> FALSE]
        /\ pc        = [i \in Procs |-> "ncs"]
        /\ unchecked = [i \in Procs |-> {}]
        /\ max       = [i \in Procs |-> 0]
        /\ nxt       = [i \in Procs |-> 1]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED <<num, flag, unchecked, max, nxt>>

e1(self) == /\ pc[self] = "e1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ max' = [max EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED <<num, nxt>>

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                 THEN /\ \E i \in unchecked[self] :
                           /\ unchecked' = [unchecked EXCEPT ![self] = @ \ {i}]
                           /\ IF num[i] > max[self]
                                THEN max' = [max EXCEPT ![self] = num[i]]
                                ELSE UNCHANGED max
                      /\ pc' = [pc EXCEPT ![self] = "e2"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                      /\ UNCHANGED <<unchecked, max>>
            /\ UNCHANGED <<num, flag, nxt>>

e3(self) == /\ pc[self] = "e3"
            /\ num' = [num EXCEPT ![self] = max[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED <<flag, unchecked, max, nxt>>

e4(self) == /\ pc[self] = "e4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED <<num, max, nxt>>

w1(self) == /\ pc[self] = "w1"
            /\ IF unchecked[self] # {}
                 THEN /\ \E i \in unchecked[self] :
                           /\ ~ flag[i]
                           /\ nxt' = [nxt EXCEPT ![self] = i]
                      /\ pc' = [pc EXCEPT ![self] = "w2"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                      /\ UNCHANGED nxt
            /\ UNCHANGED <<num, flag, unchecked, max>>

w2(self) == /\ pc[self] = "w2"
            /\ \/ num[nxt[self]] = 0
               \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
            /\ unchecked' = [unchecked EXCEPT ![self] = @ \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED <<num, flag, max, nxt>>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED <<num, flag, unchecked, max, nxt>>

exit(self) == /\ pc[self] = "exit"
              /\ num' = [num EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED <<flag, unchecked, max, nxt>>

(* Every step of a process except leaving the noncritical section *)
pFair(self) == \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
               \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

p(self) == ncs(self) \/ pFair(self)

Next == \E self \in Procs : p(self)

(***************************************************************************)
(* Fairness assumption: weak fairness on every protocol step of every      *)
(* process. Leaving ncs is not fair, so a process may stay in ncs forever. *)
(* The waits in w1 and w2 can be disabled by other processes, so they      *)
(* need strong fairness for starvation freedom to hold.                    *)
(***************************************************************************)
Fairness == \A self \in Procs :
              /\ WF_vars(pFair(self))
              /\ SF_vars(w1(self))
              /\ SF_vars(w2(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* State constraint for model checking: bound the ticket values. *)
Constraint == \A i \in Procs : num[i] <= MaxNum

-----------------------------------------------------------------------------
(* Type correctness and inspection of intermediate state *)
TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ pc \in [Procs -> Labels]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]

(* Mutual exclusion *)
MutualExclusion == \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

(* Ticket bound, checked under Constraint *)
TicketBound == \A i \in Procs : num[i] \in 0..(MaxNum + 1)

(* The choosing flag is TRUE exactly while a process is choosing its ticket *)
ChoosingFlagOK == \A i \in Procs : flag[i] <=> (pc[i] \in {"e2", "e3", "e4"})

(* Ticket is zero outside the protocol and nonzero once it has been taken *)
TicketStateOK ==
  \A i \in Procs :
    /\ (pc[i] \in {"ncs", "e1", "e2", "e3"}) => (num[i] = 0)
    /\ (pc[i] \in {"e4", "w1", "w2", "cs", "exit"}) => (num[i] > 0)

(* Scan progress: a process never scans or checks itself *)
ScanProgressOK ==
  \A i \in Procs :
    /\ (pc[i] \in {"e2", "w1", "w2"}) => (i \notin unchecked[i])
    /\ (pc[i] = "w2") => (nxt[i] # i /\ nxt[i] \in unchecked[i])

(* Lamport's inductive invariant, which captures the tie-breaking order *)
Before(i, j) ==
  /\ num[i] > 0
  /\ \/ pc[j] \in {"ncs", "e1", "exit"}
     \/ /\ pc[j] = "e2"
        /\ \/ i \in unchecked[j]
           \/ max[j] >= num[i]
     \/ /\ pc[j] = "e3"
        /\ max[j] >= num[i]
     \/ /\ pc[j] \in {"e4", "w1", "w2"}
        /\ <<num[i], i>> \prec <<num[j], j>>
        /\ (pc[j] \in {"w1", "w2"}) => (i \in unchecked[j])

OrderInv ==
  \A i \in Procs :
    /\ (pc[i] \in {"w1", "w2"}) =>
         \A j \in (Procs \ unchecked[i]) \ {i} : Before(i, j)
    /\ ( /\ pc[i] = "w2"
         /\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unchecked[nxt[i]])
            \/ pc[nxt[i]] = "e3" )
       => max[nxt[i]] >= num[i]
    /\ (pc[i] = "cs") => \A j \in Procs \ {i} : Before(i, j)

(* A process in cs holds the least <<ticket, id>> pair of all contenders *)
CSHasLeastTicket ==
  \A i, j \in Procs :
    (i # j /\ pc[i] = "cs" /\ pc[j] \in {"e4", "w1", "w2", "cs"})
      => <<num[i], i>> \prec <<num[j], j>>

(* Contenders that hold tickets have distinct <<ticket, id>> pairs *)
TieBreakTotal ==
  \A i, j \in Procs :
    (i # j /\ num[i] > 0 /\ num[j] > 0)
      => (<<num[i], i>> \prec <<num[j], j>>) # (<<num[j], j>> \prec <<num[i], i>>)

(* Absence of deadlock: if some process is in the protocol, a step is possible *)
DeadlockFree == (\E i \in Procs : pc[i] # "ncs") => ENABLED Next

Invariant == /\ TypeOK
             /\ MutualExclusion
             /\ TicketBound
             /\ ChoosingFlagOK
             /\ TicketStateOK
             /\ ScanProgressOK
             /\ OrderInv
             /\ CSHasLeastTicket
             /\ TieBreakTotal
             /\ DeadlockFree

-----------------------------------------------------------------------------
(* Liveness properties, which require Fairness *)

(* Starvation freedom: a process that tries to enter eventually enters cs *)
StarvationFree == \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

(* Deadlock freedom (liveness form): if someone is trying, someone enters *)
DeadlockFreeLive ==
  (\E i \in Procs : pc[i] = "e1") ~> (\E i \in Procs : pc[i] = "cs")

(* Ticket reset: after leaving cs, a process eventually resets its ticket *)
TicketReset == \A i \in Procs : (pc[i] = "cs") ~> (num[i] = 0 /\ pc[i] = "ncs")

THEOREM Spec => [](Invariant)
=============================================================================