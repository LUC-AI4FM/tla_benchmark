---------------------------- MODULE LockWithHistory ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Procs

VARIABLES pc, h_turn, s

vars == <<pc, h_turn, s>>

--------------------------------------------------------------------------------
(* Process states in the lock protocol *)
(* States: "idle", "trying", "critical", "exiting" *)

--------------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ h_turn = CHOOSE p \in Procs : TRUE  \* Arbitrary initial turn
    /\ s = [p \in Procs |-> 0]  \* Stuttering counter for three-step entry

--------------------------------------------------------------------------------
(* Transition Actions *)

(* First step of entry protocol - process declares interest *)
TryStep1(p) ==
    /\ pc[p] = "idle"
    /\ s[p] = 0
    /\ s' = [s EXCEPT ![p] = 1]
    /\ pc' = pc
    /\ h_turn' = h_turn

(* Second step of entry protocol - process sets turn *)
TryStep2(p) ==
    /\ pc[p] = "idle"
    /\ s[p] = 1
    /\ s' = [s EXCEPT ![p] = 2]
    /\ h_turn' = p  \* History variable tracks turn assignment
    /\ pc' = pc

(* Third step of entry protocol - process moves to trying *)
TryStep3(p) ==
    /\ pc[p] = "idle"
    /\ s[p] = 2
    /\ s' = [s EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ h_turn' = h_turn

(* Combined try action for three-step entry *)
Try(p) ==
    \/ TryStep1(p)
    \/ TryStep2(p)
    \/ TryStep3(p)

(* Enter critical section when conditions allow *)
(* A process can enter if no other process is in critical or 
   if it's not the one who last set the turn *)
Enter(p) ==
    /\ pc[p] = "trying"
    /\ \/ \A q \in Procs \ {p} : pc[q] \in {"idle", "exiting"}
       \/ h_turn # p
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ h_turn' = h_turn
    /\ s' = s

(* Exit critical section *)
Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "exiting"]
    /\ h_turn' = h_turn
    /\ s' = s

(* Return to idle state *)
Return(p) ==
    /\ pc[p] = "exiting"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ h_turn' = h_turn
    /\ s' = s

--------------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \E p \in Procs :
        \/ Try(p)
        \/ Enter(p)
        \/ Exit(p)
        \/ Return(p)

--------------------------------------------------------------------------------
(* Fairness conditions *)

Fairness ==
    /\ \A p \in Procs : WF_vars(TryStep1(p))
    /\ \A p \in Procs : WF_vars(TryStep2(p))
    /\ \A p \in Procs : WF_vars(TryStep3(p))
    /\ \A p \in Procs : WF_vars(Enter(p))
    /\ \A p \in Procs : WF_vars(Exit(p))
    /\ \A p \in Procs : WF_vars(Return(p))

--------------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
(* Safety Invariants *)

(* Type invariant *)
TypeOK ==
    /\ pc \in [Procs -> {"idle", "trying", "critical", "exiting"}]
    /\ h_turn \in Procs
    /\ s \in [Procs -> 0..2]

(* Mutual exclusion: at most one process in critical section *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "critical" /\ pc[q] = "critical")

(* At most one process in critical or exiting *)
AtMostOneCritical ==
    Cardinality({p \in Procs : pc[p] = "critical"}) <= 1

--------------------------------------------------------------------------------
(* Liveness Properties *)

(* Every trying process eventually enters critical section *)
Liveness ==
    \A p \in Procs : (pc[p] = "trying") ~> (pc[p] = "critical")

(* Every process in critical section eventually exits *)
Progress ==
    \A p \in Procs : (pc[p] = "critical") ~> (pc[p] = "idle")

--------------------------------------------------------------------------------
(* Peterson specification mapping *)
(* These definitions map Lock states to Peterson states for refinement *)

(* Map pc and s to Peterson's flag variable *)
flag_map ==
    [p \in Procs |->
        CASE pc[p] = "idle" /\ s[p] = 0 -> FALSE
          [] pc[p] = "idle" /\ s[p] >= 1 -> TRUE
          [] pc[p] = "trying" -> TRUE
          [] pc[p] = "critical" -> TRUE
          [] pc[p] = "exiting" -> FALSE
          [] OTHER -> FALSE]

(* Map pc and s to Peterson's pc states *)
(* Peterson states: "ncs", "setflag", "setturn", "check", "cs", "resetflag" *)
peterson_pc_map ==
    [p \in Procs |->
        CASE pc[p] = "idle" /\ s[p] = 0 -> "ncs"
          [] pc[p] = "idle" /\ s[p] = 1 -> "setflag"
          [] pc[p] = "idle" /\ s[p] = 2 -> "setturn"
          [] pc[p] = "trying" -> "check"
          [] pc[p] = "critical" -> "cs"
          [] pc[p] = "exiting" -> "resetflag"
          [] OTHER -> "ncs"]

--------------------------------------------------------------------------------
(* Invariant combining all safety properties *)
SafetyInvariant ==
    /\ TypeOK
    /\ MutualExclusion

================================================================================