---------------------------- MODULE LockWithAux ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Procs

VARIABLES pc, turn, h_turn, s

vars == <<pc, turn, h_turn, s>>

-----------------------------------------------------------------------------
(* Process states in the lock protocol *)
(* pc[p] \in {"idle", "trying", "critical"} *)

(* Stuttering counter: each process needs to take 3 steps to enter critical section *)
(* s[p] \in 0..2 tracks which step of the entry protocol process p is on *)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ turn \in Procs
    /\ h_turn = turn
    /\ s = [p \in Procs |-> 0]

-----------------------------------------------------------------------------
(* Transition actions *)

(* Process p starts trying to enter critical section - first step of entry protocol *)
TryStep1(p) ==
    /\ pc[p] = "idle"
    /\ s[p] = 0
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ s' = [s EXCEPT ![p] = 1]
    /\ turn' = turn
    /\ h_turn' = h_turn

(* Process p continues entry protocol - second step (sets turn) *)
TryStep2(p) ==
    /\ pc[p] = "trying"
    /\ s[p] = 1
    /\ turn' = p
    /\ h_turn' = p
    /\ s' = [s EXCEPT ![p] = 2]
    /\ pc' = pc

(* Process p completes entry protocol - third step (checks turn and possibly enters) *)
TryStep3(p) ==
    /\ pc[p] = "trying"
    /\ s[p] = 2
    /\ \A q \in Procs \ {p} : pc[q] # "critical"
    /\ turn # p \/ (\A q \in Procs \ {p} : pc[q] # "trying")
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ s' = [s EXCEPT ![p] = 0]
    /\ turn' = turn
    /\ h_turn' = h_turn

(* Process p waits (stuttering step when cannot enter) *)
Wait(p) ==
    /\ pc[p] = "trying"
    /\ s[p] = 2
    /\ turn = p
    /\ \E q \in Procs \ {p} : pc[q] = "trying"
    /\ s' = [s EXCEPT ![p] = 2]
    /\ pc' = pc
    /\ turn' = turn
    /\ h_turn' = h_turn

(* Process p exits critical section *)
Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ s' = s
    /\ turn' = turn
    /\ h_turn' = h_turn

-----------------------------------------------------------------------------
(* Combined process actions *)

ProcAction(p) ==
    \/ TryStep1(p)
    \/ TryStep2(p)
    \/ TryStep3(p)
    \/ Wait(p)
    \/ Exit(p)

Next == \E p \in Procs : ProcAction(p)

-----------------------------------------------------------------------------
(* Fairness conditions *)

Fairness == \A p \in Procs : WF_vars(ProcAction(p))

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

TypeOK ==
    /\ pc \in [Procs -> {"idle", "trying", "critical"}]
    /\ turn \in Procs
    /\ h_turn \in Procs
    /\ s \in [Procs -> 0..2]

(* Mutual exclusion: at most one process in critical section *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "critical" /\ pc[q] = "critical")

(* History variable tracks turn correctly *)
HistoryConsistent ==
    h_turn = turn \/ (\E p \in Procs : s[p] = 1)

(* Invariant combining all safety properties *)
Invariant ==
    /\ TypeOK
    /\ MutualExclusion

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* Every process that tries eventually enters critical section *)
Liveness ==
    \A p \in Procs : (pc[p] = "trying") ~> (pc[p] = "critical")

(* No starvation *)
NoStarvation ==
    \A p \in Procs : [](pc[p] = "trying" => <>(pc[p] = "critical"))

=============================================================================