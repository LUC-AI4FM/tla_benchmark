-------------------------- MODULE Bakery --------------------------
EXTENDS Integers, TLC

CONSTANTS NumProcs, MaxTicket

ASSUME (NumProcs \in 1..127) /\ (MaxTicket \in 1..127)

Procs == 1..NumProcs

VARIABLES pc, number, choosing

vars == <<pc, number, choosing>>

\* The state of a process i is given by pc[i]:
\* "ncs":  Non-critical section
\* "L1":   In the process of choosing a ticket number (choosing[i] is TRUE)
\* "L2":   Has a ticket, waiting to enter the critical section (choosing[i] is FALSE)
\* "cs":   In the critical section

\* Helper operator to find the maximum value in the range of a function.
Max(f) ==
  LET S == {f[i] : i \in DOMAIN f}
  IN IF S = {} THEN 0 ELSE CHOOSE n \in S : \A m \in S : n >= m

\* Type invariant for model checking.
TypeOK ==
  /\ pc \in [Procs -> {"ncs", "L1", "L2", "cs"}]
  /\ number \in [Procs -> 0..MaxTicket]
  /\ choosing \in [Procs -> BOOLEAN]

Init ==
  /\ pc = [i \in Procs |-> "ncs"]
  /\ number = [i \in Procs |-> 0]
  /\ choosing = [i \in Procs |-> FALSE]

\* Process i requests entry: sets choosing flag and picks a ticket number.
\* The ticket number is bounded by MaxTicket for model checking.
ncs_to_L1(i) ==
  /\ pc[i] = "ncs"
  /\ LET new_num == 1 + Max(number)
     IN new_num <= MaxTicket
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ number' = [number EXCEPT ![i] = 1 + Max(number)]
  /\ pc' = [pc EXCEPT ![i] = "L1"]

\* Process i finishes choosing its number and is ready to wait.
L1_to_L2(i) ==
  /\ pc[i] = "L1"
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "L2"]
  /\ UNCHANGED <<number>>

\* Lexicographical comparison of tickets (number, proc_id).
lt(p1, p2) == (p1[1] < p2[1]) \/ (p1[1] = p2[1] /\ p1[2] < p2[2])
lte(p1, p2) == lt(p1, p2) \/ (p1 = p2)

\* Process i enters the critical section if its ticket is the smallest among
\* all processes that are not in the middle of choosing a ticket.
L2_to_cs(i) ==
  /\ pc[i] = "L2"
  /\ \A j \in Procs :
       choosing[j] = FALSE /\ (number[j] = 0 \/ lte(<<number[i], i>>, <<number[j], j>>))
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<number, choosing>>

\* Process i exits the critical section and resets its ticket.
cs_to_ncs(i) ==
  /\ pc[i] = "cs"
  /\ number' = [number EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED <<choosing>>

\* An action for a single process.
Process(i) ==
    \/ ncs_to_L1(i)
    \/ L1_to_L2(i)
    \/ L2_to_cs(i)
    \/ cs_to_ncs(i)

\* The next-state relation for the entire system.
Next == \E i \in Procs : Process(i)

\* The fairness property, ensuring each process makes progress if enabled.
Fairness == \A i \in Procs : WF_vars(Process(i))

\* The main specification.
Spec == Init /\ [][Next]_vars /\ Fairness

\* The safety property: mutual exclusion.
MutualExclusion ==
  \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* The invariant to be checked by TLC.
Invariant == MutualExclusion

=============================================================================