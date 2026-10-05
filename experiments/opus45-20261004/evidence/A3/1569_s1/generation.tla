---------------------------- MODULE BakeryAlgorithm ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Procs, MaxTicketValue

VARIABLES num, flag, localNum, localMax, localJ, pc

vars == <<num, flag, localNum, localMax, localJ, pc>>

------------------------------------------------------------------------------
(* Type definitions and helpers *)

ProcSet == Procs

Max(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y

(* Lexicographic ordering: (a, i) << (b, j) *)
\* Process i has priority over j if i's ticket is smaller, or equal ticket but smaller id
HasPriority(i, j) ==
    \/ num[i] < num[j]
    \/ (num[i] = num[j] /\ i < j)

------------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ num = [p \in Procs |-> 0]
    /\ flag = [p \in Procs |-> FALSE]
    /\ localNum = [p \in Procs |-> [q \in Procs |-> 0]]
    /\ localMax = [p \in Procs |-> 0]
    /\ localJ = [p \in Procs |-> CHOOSE p0 \in Procs : TRUE]
    /\ pc = [p \in Procs |-> "ncs"]

------------------------------------------------------------------------------
(* Actions for each process *)

(* Non-critical section - process decides to enter *)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED <<num, flag, localNum, localMax, localJ>>

(* Start entering: set flag to true *)
enter(self) ==
    /\ pc[self] = "enter"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "read_nums"]
    /\ localNum' = [localNum EXCEPT ![self] = [q \in Procs |-> 0]]
    /\ localMax' = [localMax EXCEPT ![self] = 0]
    /\ localJ' = [localJ EXCEPT ![self] = CHOOSE p0 \in Procs : TRUE]
    /\ UNCHANGED <<num>>

(* Read all ticket numbers to find maximum *)
read_nums(self) ==
    /\ pc[self] = "read_nums"
    /\ localNum' = [localNum EXCEPT ![self] = num]
    /\ localMax' = [localMax EXCEPT ![self] = Max({num[q] : q \in Procs})]
    /\ pc' = [pc EXCEPT ![self] = "choose_ticket"]
    /\ UNCHANGED <<num, flag, localJ>>

(* Choose ticket number: max + 1 *)
choose_ticket(self) ==
    /\ pc[self] = "choose_ticket"
    /\ num' = [num EXCEPT ![self] = localMax[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "unset_flag"]
    /\ UNCHANGED <<flag, localNum, localMax, localJ>>

(* Unset choosing flag *)
unset_flag(self) ==
    /\ pc[self] = "unset_flag"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ localJ' = [localJ EXCEPT ![self] = CHOOSE p0 \in Procs : TRUE]
    /\ pc' = [pc EXCEPT ![self] = "wait_loop"]
    /\ UNCHANGED <<num, localNum, localMax>>

(* Wait loop: check each other process *)
wait_loop(self) ==
    /\ pc[self] = "wait_loop"
    /\ IF \A j \in Procs \ {self} : 
          /\ ~flag[j]
          /\ (num[j] = 0 \/ HasPriority(self, j))
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "check_flag"]
    /\ UNCHANGED <<num, flag, localNum, localMax, localJ>>

(* Check if other process j is choosing *)
check_flag(self) ==
    /\ pc[self] = "check_flag"
    /\ \E j \in Procs \ {self} :
        /\ localJ' = [localJ EXCEPT ![self] = j]
        /\ IF flag[j]
           THEN pc' = [pc EXCEPT ![self] = "check_flag"]
           ELSE pc' = [pc EXCEPT ![self] = "check_turn"]
    /\ UNCHANGED <<num, flag, localNum, localMax>>

(* Check if it's our turn compared to process j *)
check_turn(self) ==
    /\ pc[self] = "check_turn"
    /\ LET j == localJ[self]
       IN IF num[j] = 0 \/ HasPriority(self, j)
          THEN pc' = [pc EXCEPT ![self] = "wait_loop"]
          ELSE pc' = [pc EXCEPT ![self] = "check_flag"]
    /\ UNCHANGED <<num, flag, localNum, localMax, localJ>>

(* Critical section *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<num, flag, localNum, localMax, localJ>>

(* Exit critical section: reset ticket to 0 *)
exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<flag, localNum, localMax, localJ>>

------------------------------------------------------------------------------
(* Process action *)

proc(self) ==
    \/ ncs(self)
    \/ enter(self)
    \/ read_nums(self)
    \/ choose_ticket(self)
    \/ unset_flag(self)
    \/ wait_loop(self)
    \/ check_flag(self)
    \/ check_turn(self)
    \/ cs(self)
    \/ exit(self)

------------------------------------------------------------------------------
(* Next state relation *)

Next == \E self \in Procs : proc(self)

------------------------------------------------------------------------------
(* Fairness *)

Fairness == \A self \in Procs : WF_vars(proc(self))

------------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

------------------------------------------------------------------------------
(* Safety Invariants *)

(* Type invariant *)
TypeOK ==
    /\ num \in [Procs -> Nat]
    /\ flag \in [Procs -> BOOLEAN]
    /\ localNum \in [Procs -> [Procs -> Nat]]
    /\ localMax \in [Procs -> Nat]
    /\ localJ \in [Procs -> Procs]
    /\ pc \in [Procs -> {"ncs", "enter", "read_nums", "choose_ticket", 
                         "unset_flag", "wait_loop", "check_flag", 
                         "check_turn", "cs", "exit"}]

(* Mutual Exclusion: at most one process in critical section *)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Alternative formulation: cardinality of processes in CS is at most 1 *)
MutexInvariant ==
    Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

------------------------------------------------------------------------------
(* State Constraint for TLC Model Checking *)

StateConstraint ==
    \A p \in Procs : num[p] <= MaxTicketValue

------------------------------------------------------------------------------
(* Liveness Properties *)

(* Every process that wants to enter the critical section eventually does *)
Liveness ==
    \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

(* Starvation freedom: if a process is trying to enter, it eventually enters CS *)
StarvationFreedom ==
    \A p \in Procs : (pc[p] \in {"enter", "read_nums", "choose_ticket", 
                                  "unset_flag", "wait_loop", "check_flag", 
                                  "check_turn"}) ~> (pc[p] = "cs")

================================================================================