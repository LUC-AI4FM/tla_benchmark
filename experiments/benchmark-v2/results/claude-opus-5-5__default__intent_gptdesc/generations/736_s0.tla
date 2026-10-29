---------------------------- MODULE BoundedBakery ----------------------------
(***************************************************************************)
(* Bounded version of Lamport's Bakery mutual-exclusion algorithm.        *)
(*                                                                         *)
(* N processes cycle through the following local states:                  *)
(*   "ncs"    - thinking (noncritical section)                             *)
(*   "try"    - wishes to enter; waits until a ticket can be drawn without *)
(*              overflowing the bounded ticket domain 0..MaxTicket         *)
(*   "choose" - doorway: choosing[i] = TRUE while the ticket is drawn      *)
(*   "wait"   - holds a ticket; compares it with every other process      *)
(*   "cs"     - in the critical section                                    *)
(*   "exit"   - leaving; releases its ticket (num[i] := 0)                 *)
(*                                                                         *)
(* Boundedness:                                                            *)
(* A process may enter the doorway only if                                 *)
(*     MaxNum + #choosing + 1 =< MaxTicket                                 *)
(* where MaxNum is the largest ticket currently held and #choosing is the  *)
(* number of processes currently in the doorway. Each process in the      *)
(* doorway can raise the maximum ticket by at most one, so the invariant   *)
(*     MaxNum + #choosing =< MaxTicket                                     *)
(* holds in every reachable state. As a result, a ticket drawn in the      *)
(* doorway never exceeds MaxTicket, and a process never blocks inside the  *)
(* doorway with choosing = TRUE.                                           *)
(*                                                                         *)
(* Tickets are compared lexicographically on <<ticket, process id>>, so    *)
(* equal tickets are broken by process id.                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,          \* number of processes
          MaxTicket   \* largest ticket value permitted

ASSUME NAssump   == N \in Nat \ {0}
ASSUME MaxAssump == MaxTicket \in Nat \ {0}

Procs   == 1 .. N
Tickets == 0 .. MaxTicket          \* 0 means "no ticket"
States  == {"ncs", "try", "choose", "wait", "cs", "exit"}

VARIABLES num,        \* num[i]       : current ticket of process i
          choosing,   \* choosing[i]  : TRUE while i is in the doorway
          unchecked,  \* unchecked[i] : processes that i has not yet passed
          pc          \* pc[i]        : local control state of process i

vars == <<num, choosing, unchecked, pc>>

-----------------------------------------------------------------------------
(* Helper operators *)

SetMax(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : y <= x

MaxNum == SetMax({num[j] : j \in Procs})

NumChoosing == Cardinality({j \in Procs : choosing[j]})

\* Lexicographic order on <<ticket, id>>. This gives the tie-break rule.
LexLess(a, b) == \/ a[1] < b[1]
                 \/ a[1] = b[1] /\ a[2] < b[2]

\* i has priority over j
Before(i, j) == LexLess(<<num[i], i>>, <<num[j], j>>)

-----------------------------------------------------------------------------
Init == /\ num       = [i \in Procs |-> 0]
        /\ choosing  = [i \in Procs |-> FALSE]
        /\ unchecked = [i \in Procs |-> {}]
        /\ pc        = [i \in Procs |-> "ncs"]

\* Leave the noncritical section. This step is not fair, so a process may
\* stay in "ncs" forever.
Request(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "try"]
    /\ UNCHANGED <<num, choosing, unchecked>>

\* Enter the doorway only when the ticket domain still has room.
Try(i) ==
    /\ pc[i] = "try"
    /\ MaxNum + NumChoosing + 1 <= MaxTicket
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ pc'       = [pc EXCEPT ![i] = "choose"]
    /\ UNCHANGED <<num, unchecked>>

\* Draw ticket = 1 + maximum ticket held by the other processes.
TakeTicket(i) ==
    /\ pc[i] = "choose"
    /\ LET t == 1 + SetMax({num[j] : j \in Procs \ {i}})
       IN  /\ t <= MaxTicket          \* always true, by the budget invariant
           /\ num' = [num EXCEPT ![i] = t]
    /\ choosing'  = [choosing EXCEPT ![i] = FALSE]
    /\ unchecked' = [unchecked EXCEPT ![i] = Procs \ {i}]
    /\ pc'        = [pc EXCEPT ![i] = "wait"]

\* Pass process j once j is not choosing and i has priority over j.
WaitStep(i) ==
    /\ pc[i] = "wait"
    /\ \E j \in unchecked[i] :
          /\ ~choosing[j]
          /\ \/ num[j] = 0
             \/ Before(i, j)
          /\ unchecked' = [unchecked EXCEPT ![i] = @ \ {j}]
    /\ UNCHANGED <<num, choosing, pc>>

EnterCS(i) ==
    /\ pc[i] = "wait"
    /\ unchecked[i] = {}
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<num, choosing, unchecked>>

ExitCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<num, choosing, unchecked>>

Release(i) ==
    /\ pc[i] = "exit"
    /\ num' = [num EXCEPT ![i] = 0]
    /\ pc'  = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<choosing, unchecked>>

Proc(i) == \/ Request(i)
           \/ Try(i)
           \/ TakeTicket(i)
           \/ WaitStep(i)
           \/ EnterCS(i)
           \/ ExitCS(i)
           \/ Release(i)

Next == \E i \in Procs : Proc(i)

\* Fairness for every step after Request. Try and WaitStep can be enabled
\* only some of the time, because their guards depend on other processes,
\* so they need strong fairness. The remaining steps stay enabled once
\* they become enabled, so weak fairness is enough.
Fairness ==
    \A i \in Procs :
        /\ SF_vars(Try(i))
        /\ WF_vars(TakeTicket(i))
        /\ SF_vars(WaitStep(i))
        /\ WF_vars(EnterCS(i))
        /\ WF_vars(ExitCS(i))
        /\ WF_vars(Release(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ num       \in [Procs -> Tickets]
    /\ choosing  \in [Procs -> BOOLEAN]
    /\ unchecked \in [Procs -> SUBSET Procs]
    /\ pc        \in [Procs -> States]

\* At most one process is in the critical section.
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Tickets always stay inside the bounded domain.
BoundedTickets == \A i \in Procs : num[i] \in 0 .. MaxTicket

\* The ticket budget, which guarantees that a drawn ticket never overflows.
TicketBudget == MaxNum + NumChoosing <= MaxTicket

\* Every comparison stays inside the bounded domain and is a strict total
\* order on distinct processes: irreflexive, total and antisymmetric.
OrderWellDefined ==
    \A i, j \in Procs :
        /\ <<num[i], i>> \in Tickets \X Procs
        /\ ~Before(i, i)
        /\ (i # j) => (Before(i, j) \/ Before(j, i))
        /\ ~(Before(i, j) /\ Before(j, i))

\* Each local state is consistent with the shared variables.
LocalStateConsistent ==
    \A i \in Procs :
        /\ choosing[i] <=> (pc[i] = "choose")
        /\ (pc[i] \in {"ncs", "try", "choose"}) => num[i] = 0
        /\ (pc[i] \in {"wait", "cs", "exit"})   => num[i] \in 1 .. MaxTicket
        /\ (pc[i] # "wait") => unchecked[i] = {}
        /\ i \notin unchecked[i]

\* Absence of deadlock: some step is always enabled.
DeadlockFree == ENABLED Next

Inv == /\ TypeOK
       /\ MutualExclusion
       /\ BoundedTickets
       /\ TicketBudget
       /\ OrderWellDefined
       /\ LocalStateConsistent
       /\ DeadlockFree

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Starvation freedom: every process that wants to enter eventually does.
StarvationFreedom ==
    \A i \in Procs : (pc[i] \in {"try", "choose", "wait"}) ~> (pc[i] = "cs")

\* Global progress: if anyone is trying, someone eventually enters.
DeadlockFreedomLiveness ==
    (\E i \in Procs : pc[i] \in {"try", "choose", "wait"})
        ~> (\E i \in Procs : pc[i] = "cs")

\* A process in the critical section eventually returns to "ncs",
\* releasing its ticket.
EventualRelease ==
    \A i \in Procs : (pc[i] = "cs") ~> (pc[i] = "ncs" /\ num[i] = 0)

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => StarvationFreedom /\ DeadlockFreedomLiveness /\ EventualRelease
=============================================================================