---------------------------- MODULE TwoPCwithBTM ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS RM,          \* set of resource managers
          RMMAYFAIL,   \* whether resource managers may fail
          TMMAYFAIL    \* whether the transaction manager may fail (become hidden)

ASSUME RMMAYFAIL \in BOOLEAN
ASSUME TMMAYFAIL \in BOOLEAN

VARIABLES rmState, tmState, pc

vars == << rmState, tmState, pc >>

TMID  == 0
BTMID == 10

ProcSet == RM \cup {TMID} \cup {BTMID}

-----------------------------------------------------------------------------
(* Global conditions *)

canCommit == \/ \A rmc \in RM : rmState[rmc] \in {"prepared"}
             \/ \E rm \in RM : rmState[rm] \in {"committed"}

canAbort == /\ \E rm \in RM : rmState[rm] \in {"aborted", "failed"}
            /\ ~ \E rmc \in RM : rmState[rmc] = "committed"

-----------------------------------------------------------------------------
Init == /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ pc = [self \in ProcSet |->
                    CASE self \in RM     -> "RS"
                      [] self = TMID     -> "TS"
                      [] self = BTMID    -> "BTS"]

-----------------------------------------------------------------------------
(* Resource manager *)

Prepare(p) == /\ rmState[p] = "working"
              /\ rmState' = [rmState EXCEPT ![p] = "prepared"]

Decide(p) == \/ /\ tmState = "commit"
                /\ rmState' = [rmState EXCEPT ![p] = "committed"]
             \/ /\ \/ rmState[p] = "working"
                   \/ tmState = "abort"
                /\ rmState' = [rmState EXCEPT ![p] = "aborted"]

Fail(p) == IF RMMAYFAIL
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

-----------------------------------------------------------------------------
(* Transaction manager *)

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
            ELSE UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![TMID] = "Done"]
      /\ UNCHANGED rmState

TA == /\ pc[TMID] = "TA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![TMID] = "F2"]
      /\ UNCHANGED rmState

F2 == /\ pc[TMID] = "F2"
      /\ IF TMMAYFAIL
            THEN tmState' = "hidden"
            ELSE UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![TMID] = "Done"]
      /\ UNCHANGED rmState

TManager == TS \/ TC \/ F1 \/ TA \/ F2

-----------------------------------------------------------------------------
(* Backup transaction manager *)

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

-----------------------------------------------------------------------------
(* Allow infinite stuttering to prevent deadlock on termination *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == \/ TManager
        \/ BTManager
        \/ (\E self \in RM : RManager(self))
        \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)
        /\ WF_vars(BTManager)

-----------------------------------------------------------------------------
(* Properties *)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

TypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted", "failed"}]
          /\ tmState \in {"init", "commit", "abort", "hidden"}

Consistency == \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                                      /\ rmState[rm2] = "committed"

NotCommitted == \A rm \in RM : rmState[rm] # "committed"

=============================================================================