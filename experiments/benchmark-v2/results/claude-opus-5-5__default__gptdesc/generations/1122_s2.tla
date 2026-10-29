-------------------------- MODULE TwoPhaseCommitBTM --------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS RM,          \* set of resource managers
          RMMAYFAIL,   \* whether resource managers may fail
          TMMAYFAIL    \* whether the transaction manager may fail (become hidden)

ASSUME RMMAYFAIL \in BOOLEAN
ASSUME TMMAYFAIL \in BOOLEAN
ASSUME 0 \notin RM /\ 10 \notin RM

VARIABLES rmState, tmState, pc

vars == << rmState, tmState, pc >>

TMId  == 0
BTMId == 10

ProcSet == RM \cup {TMId} \cup {BTMId}

RMStates == {"working", "prepared", "committed", "aborted", "failed"}
TMStates == {"init", "commit", "abort", "hidden"}

canCommit == \/ \A rmc \in RM : rmState[rmc] \in {"prepared"}
             \/ \E rm \in RM : rmState[rm] \in {"committed"}   \* for BTM

canAbort == /\ \E rm \in RM : rmState[rm] \in {"aborted", "failed"}
            /\ ~ \E rmc \in RM : rmState[rmc] = "committed"

Init == /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ pc = [self \in ProcSet |->
                    CASE self \in RM     -> "RS"
                      [] self = TMId     -> "TS"
                      [] self = BTMId    -> "BTS"]

-----------------------------------------------------------------------------
\* Resource manager actions

Prepare(p) == /\ rmState[p] = "working"
              /\ rmState' = [rmState EXCEPT ![p] = "prepared"]

Decide(p) == \/ /\ tmState = "commit"
                /\ rmState' = [rmState EXCEPT ![p] = "committed"]
             \/ /\ (rmState[p] = "working" \/ tmState = "abort")
                /\ rmState' = [rmState EXCEPT ![p] = "aborted"]

Fail(p) == IF RMMAYFAIL
              THEN rmState' = [rmState EXCEPT ![p] = "failed"]
              ELSE rmState' = rmState

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared"}
                  THEN /\ \/ Prepare(self)
                          \/ Decide(self)
                          \/ Fail(self)
                       /\ pc' = [pc EXCEPT ![self] = "RS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ rmState' = rmState
            /\ tmState' = tmState

RManager(self) == RS(self)

-----------------------------------------------------------------------------
\* Transaction manager actions

TS == /\ pc[TMId] = "TS"
      /\ \/ /\ canCommit
            /\ pc' = [pc EXCEPT ![TMId] = "TC"]
         \/ /\ canAbort
            /\ pc' = [pc EXCEPT ![TMId] = "TA"]
      /\ UNCHANGED << rmState, tmState >>

TC == /\ pc[TMId] = "TC"
      /\ tmState' = "commit"
      /\ pc' = [pc EXCEPT ![TMId] = "F1"]
      /\ UNCHANGED rmState

F1 == /\ pc[TMId] = "F1"
      /\ IF TMMAYFAIL
            THEN tmState' = "hidden"
            ELSE tmState' = tmState
      /\ pc' = [pc EXCEPT ![TMId] = "Done"]
      /\ UNCHANGED rmState

TA == /\ pc[TMId] = "TA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![TMId] = "F2"]
      /\ UNCHANGED rmState

F2 == /\ pc[TMId] = "F2"
      /\ IF TMMAYFAIL
            THEN tmState' = "hidden"
            ELSE tmState' = tmState
      /\ pc' = [pc EXCEPT ![TMId] = "Done"]
      /\ UNCHANGED rmState

TManager == TS \/ TC \/ F1 \/ TA \/ F2

-----------------------------------------------------------------------------
\* Backup transaction manager actions

BTS == /\ pc[BTMId] = "BTS"
       /\ \/ /\ canCommit /\ tmState = "hidden"
             /\ pc' = [pc EXCEPT ![BTMId] = "BTC"]
          \/ /\ canAbort /\ tmState = "hidden"
             /\ pc' = [pc EXCEPT ![BTMId] = "BTA"]
       /\ UNCHANGED << rmState, tmState >>

BTC == /\ pc[BTMId] = "BTC"
       /\ tmState' = "commit"
       /\ pc' = [pc EXCEPT ![BTMId] = "Done"]
       /\ UNCHANGED rmState

BTA == /\ pc[BTMId] = "BTA"
       /\ tmState' = "abort"
       /\ pc' = [pc EXCEPT ![BTMId] = "Done"]
       /\ UNCHANGED rmState

BTManager == BTS \/ BTC \/ BTA

-----------------------------------------------------------------------------
\* Termination stuttering step to avoid deadlock once all processes are done

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
\* Properties

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

TypeOK == /\ rmState \in [RM -> RMStates]
          /\ tmState \in TMStates
          /\ pc \in [ProcSet -> {"RS", "TS", "TC", "F1", "TA", "F2",
                                 "BTS", "BTC", "BTA", "Done"}]

Consistency == \A rm1, rm2 \in RM :
                  ~ /\ rmState[rm1] = "aborted"
                    /\ rmState[rm2] = "committed"

NotCommitted == \A rm \in RM : rmState[rm] # "committed"

=============================================================================