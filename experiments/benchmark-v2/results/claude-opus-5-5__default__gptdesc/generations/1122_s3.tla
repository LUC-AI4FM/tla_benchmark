------------------------------- MODULE TwoPCwithBTM -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS RM, RMMAYFAIL, TMMAYFAIL

ASSUME RMMAYFAIL \in BOOLEAN
ASSUME TMMAYFAIL \in BOOLEAN

VARIABLES rmState, tmState, pc

vars == << rmState, tmState, pc >>

TMID  == 0
BTMID == 10

ProcSet == RM \cup {TMID} \cup {BTMID}

canCommit == \/ \A rmc \in RM : rmState[rmc] \in {"prepared"}
             \/ \E rm \in RM : rmState[rm] \in {"committed"}   \* for when BTM takes over

canAbort == \A rm \in RM : rmState[rm] # "committed"

-----------------------------------------------------------------------------

Init == /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ pc = [self \in ProcSet |->
                   CASE self \in RM     -> "RS"
                     [] self = TMID     -> "TS"
                     [] self = BTMID    -> "BTS"]

(* Resource manager actions *)
Prepare(self) == /\ rmState[self] = "working"
                 /\ rmState' = [rmState EXCEPT ![self] = "prepared"]

DecideCommit(self) == /\ tmState = "commit"
                      /\ rmState' = [rmState EXCEPT ![self] = "committed"]

DecideAbort(self) == /\ \/ rmState[self] = "working"
                        \/ tmState = "abort"
                     /\ rmState' = [rmState EXCEPT ![self] = "aborted"]

Fail(self) == IF RMMAYFAIL
                THEN rmState' = [rmState EXCEPT ![self] = "failed"]
                ELSE rmState' = rmState

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared"}
                 THEN /\ \/ Prepare(self)
                         \/ DecideCommit(self)
                         \/ DecideAbort(self)
                         \/ Fail(self)
                      /\ pc' = [pc EXCEPT ![self] = "RS"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ rmState' = rmState
            /\ UNCHANGED tmState

RManager(self) == RS(self)

(* Transaction manager actions *)
TS == /\ pc[TMID] = "TS"
      /\ \/ /\ canCommit
            /\ pc' = [pc EXCEPT ![TMID] = "TC"]
         \/ /\ canAbort
            /\ pc' = [pc EXCEPT ![TMID] = "TA"]
      /\ UNCHANGED << rmState, tmState >>

TC == /\ pc[TMID] = "TC"
      /\ tmState' = "commit"
      /\ pc' = [pc EXCEPT ![TMID] = "F1"]
      /\ UNCHANGED rmState

F1 == /\ pc[TMID] = "F1"
      /\ IF TMMAYFAIL
           THEN tmState' = "hidden"
           ELSE tmState' = tmState
      /\ pc' = [pc EXCEPT ![TMID] = "Done"]
      /\ UNCHANGED rmState

TA == /\ pc[TMID] = "TA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![TMID] = "F2"]
      /\ UNCHANGED rmState

F2 == /\ pc[TMID] = "F2"
      /\ IF TMMAYFAIL
           THEN tmState' = "hidden"
           ELSE tmState' = tmState
      /\ pc' = [pc EXCEPT ![TMID] = "Done"]
      /\ UNCHANGED rmState

TManager == TS \/ TC \/ F1 \/ TA \/ F2

(* Backup transaction manager actions *)
BTS == /\ pc[BTMID] = "BTS"
       /\ \/ /\ canCommit /\ tmState = "hidden"
             /\ pc' = [pc EXCEPT ![BTMID] = "BTC"]
          \/ /\ canAbort /\ tmState = "hidden"
             /\ pc' = [pc EXCEPT ![BTMID] = "BTA"]
       /\ UNCHANGED << rmState, tmState >>

BTC == /\ pc[BTMID] = "BTC"
       /\ tmState' = "commit"
       /\ pc' = [pc EXCEPT ![BTMID] = "Done"]
       /\ UNCHANGED rmState

BTA == /\ pc[BTMID] = "BTA"
       /\ tmState' = "abort"
       /\ pc' = [pc EXCEPT ![BTMID] = "Done"]
       /\ UNCHANGED rmState

BTManager == BTS \/ BTC \/ BTA

(* Allow infinite stuttering to prevent deadlock on termination *)
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

-----------------------------------------------------------------------------

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

TypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted", "failed"}]
          /\ tmState \in {"init", "commit", "abort", "hidden"}
          /\ pc \in [ProcSet -> {"RS", "TS", "TC", "F1", "TA", "F2",
                                 "BTS", "BTC", "BTA", "Done"}]

Consistency == \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                                      /\ rmState[rm2] = "committed"

NotCommitted == \A rm \in RM : rmState[rm] # "committed"

=============================================================================