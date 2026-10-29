------------------------------ MODULE Bakery ------------------------------
(***************************************************************************)
(* Lamport's Bakery Algorithm for N processes.                             *)
(*                                                                         *)
(* Reads and writes of shared variables are modeled non-atomically: a     *)
(* process first raises its "choosing" flag. It then reads the other      *)
(* processes' tickets one at a time to compute a maximum. Next it picks a  *)
(* ticket larger than that maximum and lowers its flag. Finally it waits,  *)
(* checking each other process one at a time, until either that process   *)
(* holds no ticket or this process's <<ticket, id>> pair is lexicographically*)
(* smaller.                                                                *)
(*                                                                         *)
(* Ticket values are drawn from 0..MaxTicket so the spec can be model      *)
(* checked. Behaviors in which a process would need a ticket larger than   *)
(* MaxTicket are an artifact of the bound. Use the state constraint        *)
(* TicketConstraint and disable deadlock checking when running TLC.        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,          \* number of processes
          MaxTicket   \* bound on ticket numbers, for model checking

ASSUME NAssump  == N \in Nat \ {0}
ASSUME MaxAssump == MaxTicket \in Nat \ {0}

Procs == 1..N

\* Bounded substitute for Nat, used for ticket values
Tickets == 0..MaxTicket

\* Lexicographic ordering on <<ticket, process id>>
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1] /\ a[2] < b[2])

VARIABLES num,        \* num[p]       : ticket of process p (0 = none)
          flag,       \* flag[p]      : TRUE while p is choosing a ticket
          unchecked,  \* unchecked[p] : processes p still has to examine
          max,        \* max[p]       : largest ticket p has seen so far
          nxt,        \* nxt[p]       : process p is currently waiting on
          pc          \* pc[p]        : program counter of p

vars == << num, flag, unchecked, max, nxt, pc >>

Labels == {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}

TypeOK ==
  /\ num       \in [Procs -> Tickets]
  /\ flag      \in [Procs -> BOOLEAN]
  /\ unchecked \in [Procs -> SUBSET Procs]
  /\ max       \in [Procs -> Tickets]
  /\ nxt       \in [Procs -> Procs]
  /\ pc        \in [Procs -> Labels]

Init ==
  /\ num       = [i \in Procs |-> 0]
  /\ flag      = [i \in Procs |-> FALSE]
  /\ unchecked = [i \in Procs |-> {}]
  /\ max       = [i \in Procs |-> 0]
  /\ nxt       = [i \in Procs |-> 1]
  /\ pc        = [i \in Procs |-> "ncs"]

---------------------------------------------------------------------------
(* Noncritical section: the process may stay here forever (no fairness). *)
ncs(self) ==
  /\ pc[self] = "ncs"
  /\ pc' = [pc EXCEPT ![self] = "e1"]
  /\ UNCHANGED << num, flag, unchecked, max, nxt >>

(* Request entry: start choosing a ticket. *)
e1(self) ==
  /\ pc[self] = "e1"
  /\ flag'      = [flag EXCEPT ![self] = TRUE]
  /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
  /\ max'       = [max EXCEPT ![self] = 0]
  /\ pc'        = [pc EXCEPT ![self] = "e2"]
  /\ UNCHANGED << num, nxt >>

(* Read the other processes' tickets one at a time and compute the max. *)
e2(self) ==
  /\ pc[self] = "e2"
  /\ IF unchecked[self] # {}
       THEN \E i \in unchecked[self] :
              /\ unchecked' = [unchecked EXCEPT ![self] = @ \ {i}]
              /\ max' = [max EXCEPT ![self] =
                           IF num[i] > @ THEN num[i] ELSE @]
              /\ pc' = [pc EXCEPT ![self] = "e2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << unchecked, max >>
  /\ UNCHANGED << num, flag, nxt >>

(* Take a number larger than any ticket seen. *)
e3(self) ==
  /\ pc[self] = "e3"
  /\ \E t \in {j \in Tickets : j > max[self]} :
        num' = [num EXCEPT ![self] = t]
  /\ pc' = [pc EXCEPT ![self] = "e4"]
  /\ UNCHANGED << flag, unchecked, max, nxt >>

(* Done choosing: lower the flag and prepare to check the other processes. *)
e4(self) ==
  /\ pc[self] = "e4"
  /\ flag'      = [flag EXCEPT ![self] = FALSE]
  /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
  /\ pc'        = [pc EXCEPT ![self] = "w1"]
  /\ UNCHANGED << num, max, nxt >>

(* Choose the next process to check and wait until it is not choosing. *)
w1(self) ==
  /\ pc[self] = "w1"
  /\ IF unchecked[self] # {}
       THEN \E i \in unchecked[self] :
              /\ ~flag[i]
              /\ nxt' = [nxt EXCEPT ![self] = i]
              /\ pc'  = [pc EXCEPT ![self] = "w2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED nxt
  /\ UNCHANGED << num, flag, unchecked, max >>

(* Wait until nxt holds no ticket or self has priority over nxt. *)
w2(self) ==
  /\ pc[self] = "w2"
  /\ \/ num[nxt[self]] = 0
     \/ << num[self], self >> \prec << num[nxt[self]], nxt[self] >>
  /\ unchecked' = [unchecked EXCEPT ![self] = @ \ {nxt[self]}]
  /\ pc'        = [pc EXCEPT ![self] = "w1"]
  /\ UNCHANGED << num, flag, max, nxt >>

(* Critical section. *)
cs(self) ==
  /\ pc[self] = "cs"
  /\ pc' = [pc EXCEPT ![self] = "exit"]
  /\ UNCHANGED << num, flag, unchecked, max, nxt >>

(* Exit: release the ticket. *)
exit(self) ==
  /\ pc[self] = "exit"
  /\ num' = [num EXCEPT ![self] = 0]
  /\ pc'  = [pc EXCEPT ![self] = "ncs"]
  /\ UNCHANGED << flag, unchecked, max, nxt >>

\* All steps of a process except leaving the noncritical section
Progress(self) ==
  \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
  \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

proc(self) == ncs(self) \/ Progress(self)

Next == \E self \in Procs : proc(self)

(* Weak fairness on every step except leaving the noncritical section.   *)
(* A process may stay in its noncritical section forever, but once it    *)
(* asks for entry it keeps taking steps whenever it can.                 *)
(* w1 is not continuously enabled: it is disabled while the chosen       *)
(* process is choosing. Strong fairness is therefore used for w1 and w2. *)
Fairness ==
  \A self \in Procs :
     /\ WF_vars(Progress(self))
     /\ SF_vars(w1(self))
     /\ SF_vars(w2(self))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Model-checking aid: exclude states that use the largest ticket value, *)
(* so no process ever needs a ticket beyond the bound.                   *)
TicketConstraint == \A i \in Procs : num[i] < MaxTicket

---------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
  \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "w1", "w2"}

(* Liveness *)

DeadlockFreedom ==
  (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

StarvationFreedom ==
  \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

---------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom /\ StarvationFreedom
===========================================================================