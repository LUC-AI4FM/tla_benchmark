---------------------------- MODULE LockWithHistory ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Procs

VARIABLES pc, turn, h_turn, s

vars == <<pc, turn, h_turn, s>>

--------------------------------------------------------------------------------
(* Process states in the lock protocol *)
(* pc[p] can be: "idle", "trying", "critical", "exiting" *)

--------------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ turn \in Procs
    /\ h_turn = turn
    /\ s = [p \in Procs |-> 0]

--------------------------------------------------------------------------------
(* Actions for process p *)

(* Process p starts trying to acquire the lock *)
(* This corresponds to the first step of Peterson's entry protocol *)
TryStep1(p) ==
    /\ pc[p] = "idle"
    /\ s[p] = 0
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ s' = [s EXCEPT ![p] = 1]
    /\ UNCHANGED <<turn, h_turn>>

(* Second step of entry protocol - set turn *)
TryStep2(p) ==
    /\ pc[p] = "trying"
    /\ s[p] = 1
    /\ turn' = p
    /\ h_turn' = p
    /\ s' = [s EXCEPT ![p] = 2]
    /\ UNCHANGED pc

(* Third step of entry protocol - check condition and possibly enter critical section *)
TryStep3(p) ==
    /\ pc[p] = "trying"
    /\ s[p] = 2
    /\ \/ turn # p
       \/ \A q \in Procs \ {p} : pc[q] \in {"idle", "exiting"}
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ s' = [s EXCEPT ![p] = 0]
    /\ UNCHANGED <<turn, h_turn>>

(* Process p waits (stuttering step when condition not met) *)
Wait(p) ==
    /\ pc[p] = "trying"
    /\ s[p] = 2
    /\ turn = p
    /\ \E q \in Procs \ {p} : pc[q] \notin {"idle", "exiting"}
    /\ UNCHANGED vars

(* Process p exits the critical section *)
Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "exiting"]
    /\ UNCHANGED <<turn, h_turn, s>>

(* Process p returns to idle *)
Return(p) ==
    /\ pc[p] = "exiting"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<turn, h_turn, s>>

--------------------------------------------------------------------------------
(* Combined actions *)

Try(p) == TryStep1(p) \/ TryStep2(p) \/ TryStep3(p)

ProcAction(p) == Try(p) \/ Exit(p) \/ Return(p)

Next == \E p \in Procs : ProcAction(p)

--------------------------------------------------------------------------------
(* Fairness *)

Fairness == \A p \in Procs : WF_vars(ProcAction(p))

--------------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
(* Safety Invariants *)

TypeOK ==
    /\ pc \in [Procs -> {"idle", "trying", "critical", "exiting"}]
    /\ turn \in Procs
    /\ h_turn \in Procs
    /\ s \in [Procs -> {0, 1, 2}]

(* Mutual exclusion: at most one process in critical section *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "critical" /\ pc[q] = "critical")

(* History variable tracks turn correctly *)
HistoryConsistency ==
    h_turn = turn

(* Stuttering variable is consistent with pc *)
StutterConsistency ==
    \A p \in Procs :
        /\ (pc[p] = "idle" => s[p] = 0)
        /\ (pc[p] = "critical" => s[p] = 0)
        /\ (pc[p] = "exiting" => s[p] = 0)
        /\ (pc[p] = "trying" => s[p] \in {1, 2})

Invariant == TypeOK /\ MutualExclusion /\ StutterConsistency

--------------------------------------------------------------------------------
(* Liveness Properties *)

(* Every process that tries will eventually enter the critical section *)
Liveness == \A p \in Procs : (pc[p] = "trying") ~> (pc[p] = "critical")

(* Every process that is in critical section will eventually exit *)
Progress == \A p \in Procs : (pc[p] = "critical") ~> (pc[p] = "idle")

--------------------------------------------------------------------------------
(* Refinement mapping to Peterson's algorithm *)
(* 
   Peterson's algorithm uses:
   - flag[p]: boolean indicating p wants to enter
   - turn: which process's turn it is
   - pc states: "ncs", "set_flag", "set_turn", "check", "cs", "reset"
   
   Mapping:
   - flag[p] = (pc[p] \in {"trying", "critical"} \/ s[p] >= 1)
   - PetersonPC[p] depends on pc[p] and s[p]
*)

flag == [p \in Procs |-> pc[p] \in {"trying", "critical"} \/ s[p] >= 1]

PetersonPC == [p \in Procs |->
    CASE pc[p] = "idle" /\ s[p] = 0 -> "ncs"
      [] pc[p] = "trying" /\ s[p] = 1 -> "set_flag"
      [] pc[p] = "trying" /\ s[p] = 2 -> "check"
      [] pc[p] = "critical" -> "cs"
      [] pc[p] = "exiting" -> "reset"
      [] OTHER -> "ncs"
]

================================================================================