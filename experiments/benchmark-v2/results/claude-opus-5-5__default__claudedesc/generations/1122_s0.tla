---------------------------- MODULE 2PCwithBTM ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS RM, RMMAYFAIL, TMMAYFAIL

VARIABLES rmState, tmState, pc

vars == << rmState, tmState, pc >>

ProcSet == (RM) \cup {0} \cup {10}

RMStates == {"working", "prepared", "committed", "aborted", "failed"}
TMStates == {"init", "commit", "abort", "hidden"}

canCommit == \/ \A rmc \in RM : rmState[rmc] \in {"prepared"}
             \/ \E rm \in RM : rmState[rm] \in {"committed"}

canAbort == /\ \E rm \in RM : rmState[rm] \in {"aborted", "failed"}
            /\ ~\E rmc \in RM : rmState[rmc] = "committed"

Init == /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0    -> "TS"
                                        [] self = 10   -> "BTS"]

(* ---------------- Resource Managers ---------------- *)

Prepare(p) == /\ rmState[p] = "working"
              /\ rmState' = [rmState EXCEPT ![p] = "prepared"]

Decide(p) == \/ /\ tmState = "commit"
                /\ rmState' = [rmState EXCEPT ![p] = "committed"]
             \/ /\ (rmState[p] = "working" \/ tmState = "abort")
                /\ rmState' = [rmState EXCEPT ![p] = "aborted"]

Fail(p) == IF RMMAYFAIL /\ ~\E rm \in RM : rmState[rm] = "failed"
              THEN rmState' = [rmState EXCEPT ![p] = "failed"]
              ELSE UNCHANGED rmState

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared"}
                  THEN /\ \/ Prepare(self)
                          \/ Decide(self)
                          \/ Fail(self)
                       /\ pc' = [pc EXCEPT ![self] = "RS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmState
            /\ UNCHANGED tmState

RManager(self) == RS(self)

(* ---------------- Primary Transaction Manager ---------------- *)

TS == /\ pc[0] = "TS"
      /\ \/ /\ canCommit
            /\ pc' = [pc EXCEPT ![0] = "TC"]
         \/ /\ canAbort
            /\ pc' = [pc EXCEPT ![0] = "TA"]
      /\ UNCHANGED << rmState, tmState >>

TC == /\ pc[0] = "TC"
      /\ tmState' = "commit"
      /\ pc' = [pc EXCEPT ![0] = "F1"]
      /\ UNCHANGED rmState

F1 == /\ pc[0] = "F1"
      /\ IF TMMAYFAIL
            THEN tmState' = "hidden"
            ELSE UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TA == /\ pc[0] = "TA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![0] = "F2"]
      /\ UNCHANGED rmState

F2 == /\ pc[0] = "F2"
      /\ IF TMMAYFAIL
            THEN tmState' = "hidden"
            ELSE UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TManager == TS \/ TC \/ F1 \/ TA \/ F2

(* ---------------- Backup Transaction Manager ---------------- *)

BTS == /\ pc[10] = "BTS"
       /\ \/ /\ canCommit /\ tmState = "hidden"
             /\ pc' = [pc EXCEPT ![10] = "BTC"]
          \/ /\ canAbort /\ tmState = "hidden"
             /\ pc' = [pc EXCEPT ![10] = "BTA"]
       /\ UNCHANGED << rmState, tmState >>

BTC == /\ pc[10] = "BTC"
       /\ tmState' = "commit"
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED rmState

BTA == /\ pc[10] = "BTA"
       /\ tmState' = "abort"
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED rmState

BTManager == BTS \/ BTC \/ BTA

(* ---------------- Specification ---------------- *)

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == \/ TManager
        \/ BTManager
        \/ (\E self \in RM : RManager(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)
        /\ WF_vars(BTManager)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

(* ---------------- Properties ---------------- *)

TypeOK == /\ rmState \in [RM -> RMStates]
          /\ tmState \in TMStates

Consistency == \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                                      /\ rmState[rm2] = "committed"

NotCommitted == \A rm \in RM : rmState[rm] # "committed"

=============================================================================