------------------------------- MODULE Bakery -------------------------------
(***************************************************************************)
(* Lamport's Bakery algorithm for N processes and one critical section.    *)
(*                                                                         *)
(* Each process p runs the following protocol. Every labelled step is one *)
(* atomic action, so steps of different processes interleave freely.      *)
(*                                                                         *)
(*   ncs : non-critical section. The process may stay here forever.        *)
(*   e1  : choosing[p] := TRUE; start scanning the other processes.        *)
(*   e2  : read num[i] for one unscanned process i and keep the maximum.   *)
(*         Repeat until every other process has been read.                 *)
(*   e3  : num[p] := maxSeen[p] + 1 (the ticket).                          *)
(*         If that value would exceed MaxTicket, restart the scan instead. *)
(*         This retry exists only to keep the state space finite. It       *)
(*         never breaks safety, because flag[p] stays TRUE and num[p] = 0. *)
(*   e4  : choosing[p] := FALSE; start the waiting loop.                   *)
(*   w1  : pick an unchecked process i whose choosing flag is FALSE.       *)
(*   w2  : wait until num[i] = 0 or <<num[p],p>> precedes <<num[i],i>>     *)
(*         in lexicographic order. Then mark i as checked.                 *)
(*   cs  : critical section.                                               *)
(*   exit: num[p] := 0, then return to ncs.                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,          \* number of processes
          MaxTicket   \* upper bound on ticket values (for model checking)

ASSUME NAssump   == N \in Nat \ {0}
ASSUME BoundAssump == MaxTicket \in Nat \ {0}

Procs == 1..N

PCs == {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}

VARIABLES
    num,        \* num[p]       : ticket of p (0 means no ticket)
    flag,       \* flag[p]      : the "choosing" flag of p
    pc,         \* pc[p]        : control location of p
    unchecked,  \* unchecked[p] : processes not yet scanned or checked by p
    maxSeen,    \* maxSeen[p]   : largest ticket p has read so far in its scan
    nxt         \* nxt[p]       : process p is currently waiting on

vars == <<num, flag, pc, unchecked, maxSeen, nxt>>

(***************************************************************************)
(* Lexicographic ordering on <<ticket, process id>> pairs (tie-breaking).  *)
(***************************************************************************)
Prec(a, b) == \/ a[1] < b[1]
              \/ /\ a[1] = b[1]
                 /\ a[2] < b[2]

Before(i, j) == Prec(<<num[i], i>>, <<num[j], j>>)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Helper predicates for inspecting intermediate states.                   *)
(***************************************************************************)
Choosing(p)     == flag[p]
InDoorway(p)    == pc[p] \in {"e1", "e2", "e3", "e4"}
Scanning(p)     == pc[p] = "e2"
ScannedSet(p)   == (Procs \ {p}) \ unchecked[p]   \* scan / check progress
Waiting(p)      == pc[p] \in {"w1", "w2"}
CheckedSet(p)   == IF Waiting(p) \/ pc[p] = "cs"
                     THEN (Procs \ {p}) \ unchecked[p]
                     ELSE {}
TryingStates    == {"e1", "e2", "e3", "e4", "w1", "w2"}
Trying(p)       == pc[p] \in TryingStates

-----------------------------------------------------------------------------
Init == /\ num       = [p \in Procs |-> 0]
        /\ flag      = [p \in Procs |-> FALSE]
        /\ pc        = [p \in Procs |-> "ncs"]
        /\ unchecked = [p \in Procs |-> {}]
        /\ maxSeen   = [p \in Procs |-> 0]
        /\ nxt       = [p \in Procs |-> p]

(* Non-critical section. This step has no fairness: p may stay here forever. *)
NCS(p) == /\ pc[p] = "ncs"
          /\ pc' = [pc EXCEPT ![p] = "e1"]
          /\ UNCHANGED <<num, flag, unchecked, maxSeen, nxt>>

(* Raise the choosing flag and begin scanning the other processes. *)
E1(p) == /\ pc[p] = "e1"
         /\ flag'      = [flag EXCEPT ![p] = TRUE]
         /\ unchecked' = [unchecked EXCEPT ![p] = Procs \ {p}]
         /\ maxSeen'   = [maxSeen EXCEPT ![p] = 0]
         /\ pc'        = [pc EXCEPT ![p] = "e2"]
         /\ UNCHANGED <<num, nxt>>

(* Scan: read one other process's ticket per step, in any order. *)
E2(p) == /\ pc[p] = "e2"
         /\ \/ /\ unchecked[p] # {}
               /\ \E i \in unchecked[p] :
                    /\ unchecked' = [unchecked EXCEPT ![p] = @ \ {i}]
                    /\ maxSeen'   = [maxSeen EXCEPT ![p] =
                                       IF num[i] > @ THEN num[i] ELSE @]
               /\ UNCHANGED <<num, flag, pc, nxt>>
            \/ /\ unchecked[p] = {}
               /\ pc' = [pc EXCEPT ![p] = "e3"]
               /\ UNCHANGED <<num, flag, unchecked, maxSeen, nxt>>

(* Take ticket maxSeen + 1. If that exceeds the bound, restart the scan. *)
E3(p) == /\ pc[p] = "e3"
         /\ \/ /\ maxSeen[p] + 1 <= MaxTicket
               /\ num' = [num EXCEPT ![p] = maxSeen[p] + 1]
               /\ pc'  = [pc EXCEPT ![p] = "e4"]
               /\ UNCHANGED <<flag, unchecked, maxSeen, nxt>>
            \/ /\ maxSeen[p] + 1 > MaxTicket
               /\ unchecked' = [unchecked EXCEPT ![p] = Procs \ {p}]
               /\ maxSeen'   = [maxSeen EXCEPT ![p] = 0]
               /\ pc'        = [pc EXCEPT ![p] = "e2"]
               /\ UNCHANGED <<num, flag, nxt>>

(* Lower the choosing flag and begin the waiting loop. *)
E4(p) == /\ pc[p] = "e4"
         /\ flag'      = [flag EXCEPT ![p] = FALSE]
         /\ unchecked' = [unchecked EXCEPT ![p] = Procs \ {p}]
         /\ pc'        = [pc EXCEPT ![p] = "w1"]
         /\ UNCHANGED <<num, maxSeen, nxt>>

(* Wait loop, part 1: pick an unchecked process that is not choosing. *)
W1(p) == /\ pc[p] = "w1"
         /\ \/ /\ unchecked[p] # {}
               /\ \E i \in unchecked[p] :
                    /\ ~flag[i]
                    /\ nxt' = [nxt EXCEPT ![p] = i]
               /\ pc' = [pc EXCEPT ![p] = "w2"]
               /\ UNCHANGED <<num, flag, unchecked, maxSeen>>
            \/ /\ unchecked[p] = {}
               /\ pc' = [pc EXCEPT ![p] = "cs"]
               /\ UNCHANGED <<num, flag, unchecked, maxSeen, nxt>>

(* Wait loop, part 2: wait until nxt[p] has no ticket or a later one. *)
W2(p) == /\ pc[p] = "w2"
         /\ \/ num[nxt[p]] = 0
            \/ Before(p, nxt[p])
         /\ unchecked' = [unchecked EXCEPT ![p] = @ \ {nxt[p]}]
         /\ pc'        = [pc EXCEPT ![p] = "w1"]
         /\ UNCHANGED <<num, flag, maxSeen, nxt>>

(* Leave the critical section. *)
CS(p) == /\ pc[p] = "cs"
         /\ pc' = [pc EXCEPT ![p] = "exit"]
         /\ UNCHANGED <<num, flag, unchecked, maxSeen, nxt>>

(* Release the ticket. *)
Exit(p) == /\ pc[p] = "exit"
           /\ num' = [num EXCEPT ![p] = 0]
           /\ pc'  = [pc EXCEPT ![p] = "ncs"]
           /\ UNCHANGED <<flag, unchecked, maxSeen, nxt>>

(* Every step after leaving ncs. These steps are the ones made fair. *)
ProtocolStep(p) == E1(p) \/ E2(p) \/ E3(p) \/ E4(p) \/ W1(p) \/ W2(p)
                   \/ CS(p) \/ Exit(p)

Proc(p) == NCS(p) \/ ProtocolStep(p)

Next == \E p \in Procs : Proc(p)

(***************************************************************************)
(* Fairness: weak fairness on each process's protocol steps only.          *)
(* No fairness applies to NCS, so a process may stay in ncs forever.       *)
(* A process in cs leaves it eventually, because CS(p) is weakly fair.     *)
(***************************************************************************)
Fairness == \A p \in Procs : WF_vars(ProtocolStep(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************** SAFETY *************************************)

TypeOK == /\ num       \in [Procs -> 0..MaxTicket]
          /\ flag      \in [Procs -> BOOLEAN]
          /\ pc        \in [Procs -> PCs]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ maxSeen   \in [Procs -> 0..MaxTicket]
          /\ nxt       \in [Procs -> Procs]

(* Mutual exclusion. *)
MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Ticket management: tickets stay within the bound. *)
TicketBound == \A p \in Procs : num[p] \in 0..MaxTicket

(* A process holds a ticket exactly when it is between e3 and exit. *)
TicketInv ==
  \A p \in Procs :
    /\ pc[p] \in {"ncs", "e1", "e2", "e3"} => num[p] = 0
    /\ pc[p] \in {"e4", "w1", "w2", "cs", "exit"} => num[p] \in 1..MaxTicket

(* The choosing flag is raised exactly during the doorway scan and choice. *)
ChoosingInv == \A p \in Procs : flag[p] <=> pc[p] \in {"e2", "e3", "e4"}

(* Scan and wait-loop progress. *)
ScanInv ==
  \A p \in Procs :
    /\ p \notin unchecked[p]
    /\ maxSeen[p] <= MaxTicket
    /\ pc[p] = "w2" => (nxt[p] # p /\ nxt[p] \in unchecked[p])
    /\ pc[p] = "cs" => unchecked[p] = {}

(***************************************************************************)
(* Tie-breaking order.                                                     *)
(* (a) <<ticket, id>> pairs are a strict total order on ticket holders.    *)
(* (b) A process in cs precedes every other process that holds a ticket   *)
(*     and is in e4, w1, w2 or cs.                                         *)
(* (c) A process j that is still scanning or choosing while i is in cs     *)
(*     either has not yet read i or has read a value >= num[i].            *)
(*     So j's ticket will come after i's.                                  *)
(***************************************************************************)
TotalOrderOnTickets ==
  \A i, j \in Procs :
    (i # j /\ num[i] > 0 /\ num[j] > 0) => (Before(i, j) \/ Before(j, i))

TieBreakOrder ==
  \A i, j \in Procs :
    (i # j /\ pc[i] = "cs" /\ pc[j] \in {"e4", "w1", "w2", "cs"})
       => Before(i, j)

CSDominatesDoorway ==
  \A i, j \in Procs :
    (i # j /\ pc[i] = "cs") =>
       /\ pc[j] = "e2" => (i \in unchecked[j] \/ maxSeen[j] >= num[i])
       /\ pc[j] = "e3" => maxSeen[j] >= num[i]

(* Absence of deadlock: if any process has left ncs, some step is enabled. *)
NoDeadlock ==
  (\E p \in Procs : pc[p] # "ncs") => ENABLED (\E p \in Procs : ProtocolStep(p))

Inv == /\ TypeOK
       /\ MutualExclusion
       /\ TicketBound
       /\ TicketInv
       /\ ChoosingInv
       /\ ScanInv
       /\ TotalOrderOnTickets
       /\ TieBreakOrder
       /\ CSDominatesDoorway
       /\ NoDeadlock

-----------------------------------------------------------------------------
(**************************** LIVENESS ************************************)
(* All of these properties assume Fairness (WF on each ProtocolStep(p)).  *)
(*                                                                         *)
(* Caveat on StarvationFreedom: it holds for the unbounded algorithm.      *)
(* In this bounded model, a process can in principle be forced to retry    *)
(* at e3 forever when MaxTicket is small. A counterexample that consists   *)
(* only of such e3 retries is an artifact of the bound, not of the         *)
(* algorithm.                                                              *)
(***************************************************************************)

(* Every process that starts the protocol eventually enters cs. *)
StarvationFreedom == \A p \in Procs : (pc[p] = "e1") ~> (pc[p] = "cs")

(* Deadlock freedom as progress: if some process is trying, some process *)
(* eventually enters cs.                                                 *)
DeadlockFreedom ==
  (\E p \in Procs : Trying(p)) ~> (\E p \in Procs : pc[p] = "cs")

(* Every process leaves cs eventually. *)
CSExit == \A p \in Procs : (pc[p] = "cs") ~> (pc[p] # "cs")

(* After leaving cs, a process eventually resets its ticket to 0 and *)
(* returns to ncs.                                                   *)
TicketReset ==
  \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "ncs" /\ num[p] = 0)

(* Every choosing phase eventually ends. *)
ChoosingTerminates == \A p \in Procs : (flag[p]) ~> (~flag[p])

Liveness == /\ StarvationFreedom
            /\ DeadlockFreedom
            /\ CSExit
            /\ TicketReset
            /\ ChoosingTerminates

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => Liveness
=============================================================================