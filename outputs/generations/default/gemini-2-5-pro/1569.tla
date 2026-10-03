---- MODULE Bakery ----
EXTENDS Naturals, Sequences, TLC

CONSTANT N
ASSUME N \in Nat /\ N > 0
Procs == 1..N

VARIABLES
    (* The program counter for each process *)
    pc,
    (* The ticket number for each process. 0 means no ticket. *)
    number,
    (* A flag that is TRUE while a process is choosing its ticket number. *)
    choosing,
    (* Stores the next process ID that a process needs to check in its wait loop. *)
    next_j

vars == <<pc, number, choosing, next_j>>

(* The set of control locations for each process, corresponding to PlusCal labels. *)
Labels == {"NCS", "Choosing1", "Choosing2", "Waiting", "CS"}

TypeOK ==
    /\ pc \in [Procs -> Labels]
    /\ number \in [Procs -> Nat]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ next_j \in [Procs -> 1..(N + 1)]

Init ==
    /\ pc = [p \in Procs |-> "NCS"]
    /\ number = [p \in Procs |-> 0]
    /\ choosing = [p \in Procs |-> FALSE]
    /\ next_j = [p \in Procs |-> 1]

(* Process i indicates it is about to choose a number. *)
StartChoosing(i) ==
    /\ pc[i] = "NCS"
    /\ pc' = [pc EXCEPT ![i] = "Choosing1"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<number, next_j>>

(* Process i atomically reads all ticket numbers, finds the max, and sets its own
   ticket to one greater than the max. *)
SetNumber(i) ==
    /\ pc[i] = "Choosing1"
    /\ LET max == IF Procs = {} THEN 0
                  ELSE CHOOSE m \in {number[p] : p \in Procs} :
                            \A n \in {number[p] : p \in Procs} : m >= n
       IN number' = [number EXCEPT ![i] = max + 1]
    /\ pc' = [pc EXCEPT ![i] = "Choosing2"]
    /\ UNCHANGED <<choosing, next_j>>

(* Process i finishes the choosing phase and prepares for the wait loop. *)
FinishChoosing(i) ==
    /\ pc[i] = "Choosing2"
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ next_j' = [next_j EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "Waiting"]
    /\ UNCHANGED <<number>>

(* In its wait loop, process i checks if it can proceed past process j.
   The check succeeds if j is not choosing and i has priority (lower ticket,
   or same ticket and lower ID). *)
CheckOther(i) ==
    /\ pc[i] = "Waiting"
    /\ LET j == next_j[i]
       IN /\ j \in Procs
          /\ choosing[j] = FALSE
          /\ (number[j] = 0 \/ <<number[i], i>> << <<number[j], j>>)
          /\ next_j' = [next_j EXCEPT ![i] = j + 1]
          /\ UNCHANGED <<pc, number, choosing>>

(* Process i has successfully checked all other processes and can enter the CS. *)
EnterCS(i) ==
    /\ pc[i] = "Waiting"
    /\ next_j[i] > N
    /\ pc' = [pc EXCEPT ![i] = "CS"]
    /\ UNCHANGED <<number, choosing, next_j>>

(* Process i leaves the critical section and resets its ticket. *)
ExitCS(i) ==
    /\ pc[i] = "CS"
    /\ pc' = [pc EXCEPT ![i] = "NCS"]
    /\ number' = [number EXCEPT ![i] = 0]
    /\ UNCHANGED <<choosing, next_j>>

(* A step that can be taken by process i. *)
Proc(i) ==
    \/ StartChoosing(i)
    \/ SetNumber(i)
    \/ FinishChoosing(i)
    \/ CheckOther(i)
    \/ EnterCS(i)
    \/ ExitCS(i)

(* The next-state relation for the entire system. *)
Next == \E i \in Procs : Proc(i)

(* The complete safety specification. *)
Spec == Init /\ [][Next]_vars

\* --- Invariants and Properties ---

(* The primary safety property: at most one process can be in the critical section. *)
MutualExclusion ==
    \A i, j \in Procs : (i /= j) => ~(pc[i] = "CS" /\ pc[j] = "CS")

(* A state constraint to bound the state space for model checking.
   This is not a property of the abstract algorithm, which allows ticket
   numbers to grow without bound. *)
CONSTANT MaxTicket
ASSUME MaxTicket \in Nat
TicketBound == \A p \in Procs : number[p] <= MaxTicket

=============================================================================