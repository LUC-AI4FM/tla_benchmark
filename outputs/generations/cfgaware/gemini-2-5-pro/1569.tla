---- MODULE Bakery ----
EXTENDS Integers, TLC, FiniteSets

CONSTANT NumProcs, MaxNum
ASSUME NumProcs \in 1..MaxInt
ASSUME MaxNum \in 1..MaxInt

Procs == 1..NumProcs

VARIABLES number, choosing, pc, max_of_others, other

vars == <<number, choosing, pc, max_of_others, other>>

Init == (* Global variables *)
        /\ number = [self \in Procs |-> 0]
        /\ choosing = [self \in Procs |-> FALSE]
        /\ max_of_others = [self \in Procs |-> 0]
        /\ other = [self \in Procs |-> 1]
        /\ pc = [self \in Procs |-> "ncs"]

(* Action for a process to start choosing a ticket number. *)
start_choosing(self) ==
    /\ pc[self] = "ncs"
    /\ choosing' = [choosing EXCEPT ![self] = TRUE]
    /\ max_of_others' = [max_of_others EXCEPT ![self] = 0]
    /\ other' = [other EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "start_choosing_loop"]
    /\ UNCHANGED <<number>>

(* Action for one iteration of finding the maximum ticket number. *)
start_choosing_loop_body(self) ==
    /\ pc[self] = "start_choosing_loop"
    /\ other[self] <= NumProcs
    /\ max_of_others' = [max_of_others EXCEPT ![self] =
                           IF number[other[self]] > max_of_others[self]
                           THEN number[other[self]]
                           ELSE max_of_others[self]]
    /\ other' = [other EXCEPT ![self] = other[self] + 1]
    /\ pc' = pc
    /\ UNCHANGED <<number, choosing>>

(* Action to finish choosing a ticket after checking all others. *)
finish_choosing(self) ==
    /\ pc[self] = "start_choosing_loop"
    /\ other[self] > NumProcs
    /\ number' = [number EXCEPT ![self] = max_of_others[self] + 1]
    /\ choosing' = [choosing EXCEPT ![self] = FALSE]
    /\ other' = [other EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "check_wait_loop"]
    /\ UNCHANGED <<max_of_others>>

(* Action for one iteration of waiting for this process's turn. *)
check_wait_loop_body(self) ==
    /\ pc[self] = "check_wait_loop"
    /\ other[self] <= NumProcs
    /\ choosing[other[self]] = FALSE
    /\ \/ number[other[self]] = 0
       \/ (number[self] < number[other[self]])
       \/ (number[self] = number[other[self]] /\ self < other[self])
    /\ other' = [other EXCEPT ![self] = other[self] + 1]
    /\ pc' = pc
    /\ UNCHANGED <<number, choosing, max_of_others>>

(* Action to enter the critical section after the wait loop finishes. *)
enter_critical(self) ==
    /\ pc[self] = "check_wait_loop"
    /\ other[self] > NumProcs
    /\ pc' = [pc EXCEPT ![self] = "critical"]
    /\ UNCHANGED <<number, choosing, max_of_others, other>>

(* Action to leave the critical section and reset the ticket number. *)
reset(self) ==
    /\ pc[self] = "critical"
    /\ number' = [number EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<choosing, max_of_others, other>>

(* An action for a single process. *)
ProcessAction(self) ==
    \/ start_choosing(self)
    \/ start_choosing_loop_body(self)
    \/ finish_choosing(self)
    \/ check_wait_loop_body(self)
    \/ enter_critical(self)
    \/ reset(self)

Next == \E self \in Procs : ProcessAction(self)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ number \in [Procs -> 0..MaxNum]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "start_choosing_loop", "check_wait_loop", "critical"}]
    /\ max_of_others \in [Procs -> 0..MaxNum]
    /\ other \in [Procs -> 1..(NumProcs + 1)]

MutualExclusion ==
    Cardinality({p \in Procs : pc[p] = "critical"}) <= 1

Invariant == TypeOK /\ MutualExclusion

=============================================================================