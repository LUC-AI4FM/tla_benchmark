---------------------------- MODULE LockWithHistory ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Procs

VARIABLES pc, turn, h_turn, s

vars == <<pc, turn, h_turn, s>>

--------------------------------------------------------------------------------
(* Process states in the lock protocol *)
(* States: "idle", "trying", "critical", "exiting" *)

--------------------------------------------------------------------------------
(* Helper definitions *)

OtherProc(p) == CHOOSE q \in Procs : q # p

--------------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ turn \in Procs
    /\ h_turn = turn
    /\ s = [p \in Procs |-> 0]

--------------------------------------------------------------------------------
(* Transition actions *)

(* Process p starts trying to acquire the lock *)
(* This simulates the first step of Peterson's entry protocol *)
TryEnter(p) ==
    /\ pc[p] = "idle"
    /\ s[p] = 0
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ s' = [s EXCEPT ![p] = 1]
    /\ UNCHANGED <<turn, h_turn>>

(* Stuttering step 1: simulates setting turn in Peterson's algorithm *)
StutterStep1(p) ==
    /\ pc[p] = "trying"
    /\ s[p] = 1
    /\ turn' = OtherProc(p)
    /\ h_turn' = OtherProc(p)
    /\ s' = [s EXCEPT ![p] = 2]
    /\ UNCHANGED pc

(* Stuttering step 2: simulates the wait condition check *)
StutterStep2(p) ==
    /\ pc[p] = "trying"
    /\ s[p] = 2
    /\ s' = [s EXCEPT ![p] = 3]
    /\ UNCHANGED <<pc, turn, h_turn>>

(* Process p enters critical section after completing entry protocol *)
EnterCS(p) ==
    /\ pc[p] = "trying"
    /\ s[p] = 3
    /\ \/ turn = p
       \/ pc[OtherProc(p)] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ s' = [s EXCEPT ![p] = 0]
    /\ UNCHANGED <<turn, h_turn>>

(* Process p exits critical section *)
ExitCS(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "exiting"]
    /\ UNCHANGED <<turn, h_turn, s>>

(* Process p returns to idle *)
ReturnToIdle(p) ==
    /\ pc[p] = "exiting"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<turn, h_turn, s>>

--------------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \E p \in Procs :
        \/ TryEnter(p)
        \/ StutterStep1(p)
        \/ StutterStep2(p)
        \/ EnterCS(p)
        \/ ExitCS(p)
        \/ ReturnToIdle(p)

--------------------------------------------------------------------------------
(* Fairness conditions *)

Fairness ==
    /\ \A p \in Procs : WF_vars(TryEnter(p))
    /\ \A p \in Procs : WF_vars(StutterStep1(p))
    /\ \A p \in Procs : WF_vars(StutterStep2(p))
    /\ \A p \in Procs : WF_vars(EnterCS(p))
    /\ \A p \in Procs : WF_vars(ExitCS(p))
    /\ \A p \in Procs : WF_vars(ReturnToIdle(p))

--------------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
(* Safety Invariants *)

(* Type invariant *)
TypeOK ==
    /\ pc \in [Procs -> {"idle", "trying", "critical", "exiting"}]
    /\ turn \in Procs
    /\ h_turn \in Procs
    /\ s \in [Procs -> 0..3]

(* Mutual exclusion: at most one process in critical section *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "critical" /\ pc[q] = "critical")

(* History variable tracks turn correctly *)
HistoryConsistency ==
    h_turn = turn

(* Stuttering counter is valid for the current state *)
StutterValid ==
    \A p \in Procs :
        /\ (pc[p] = "idle" => s[p] = 0)
        /\ (pc[p] = "trying" => s[p] \in 1..3)
        /\ (pc[p] = "critical" => s[p] = 0)
        /\ (pc[p] = "exiting" => s[p] = 0)

--------------------------------------------------------------------------------
(* Liveness Properties *)

(* Every process that tries eventually enters the critical section *)
Liveness ==
    \A p \in Procs : (pc[p] = "trying") ~> (pc[p] = "critical")

(* Starvation freedom *)
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "idle") ~> (pc[p] = "critical")

--------------------------------------------------------------------------------
(* Peterson specification refinement mapping *)
(* This relates the lock protocol with history to Peterson's algorithm *)

(* Map lock states to Peterson states *)
PetersonPC(p) ==
    CASE pc[p] = "idle" -> "ncs"
      [] pc[p] = "trying" /\ s[p] = 1 -> "e1"
      [] pc[p] = "trying" /\ s[p] = 2 -> "e2"
      [] pc[p] = "trying" /\ s[p] = 3 -> "e3"
      [] pc[p] = "critical" -> "cs"
      [] pc[p] = "exiting" -> "e4"
      [] OTHER -> "ncs"

(* Flag variable for Peterson (derived) *)
PetersonFlag(p) ==
    pc[p] \in {"trying", "critical", "exiting"}

--------------------------------------------------------------------------------

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness

================================================================================