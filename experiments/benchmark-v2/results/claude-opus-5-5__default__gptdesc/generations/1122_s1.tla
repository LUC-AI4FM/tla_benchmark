---------------------------- MODULE TwoPCwithBTM ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS RM,          \* The set of resource managers
          RMMAYFAIL,   \* Whether resource managers may fail
          TMMAYFAIL    \* Whether the transaction manager may fail (become hidden)

ASSUME RMMAYFAIL \in BOOLEAN
ASSUME TMMAYFAIL \in BOOLEAN
ASSUME RM \cap {0, 10} = {}

VARIABLES rmState, tmState, pc

vars == << rmState, tmState, pc >>

ProcSet == RM \cup {0} \cup {10}

\* Global decision conditions
canCommit == \/ \A rmc \in RM : rmState[rmc] \in {"prepared"}
             \/ \E rm \in RM : rmState[rm] \in {"committed"}

canAbort == /\ \E rm \in RM : rmState[rm] \in {"aborted", "failed"}
            /\ ~\E rmc \in RM : rmState[rmc] = "committed"

Init == /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0   -> "TS"
                                        [] self = 10  -> "BTS"]

-----------------------------------------------------------------------------
\* Resource manager actions

Prepare(p) == /\ rmState[p] = "working"
              /\ rmState' = [rmState EXCEPT ![p] = "prepared"]

Decide(p) == \/ /\ tmState = "commit"
                /\ rmState' = [rmState EXCEPT ![p] = "committed"]
             \/ /\ rmState[p] = "working" \/ tmState = "abort"
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
                      /\ UNCHANGED rmState
            /\ UNCHANGED tmState

RManager(self) == RS(self)

-----------------------------------------------------------------------------
\* Transaction manager actions

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

-----------------------------------------------------------------------------
\* Backup transaction manager actions

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

-----------------------------------------------------------------------------

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

TypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted", "failed"}]
          /\ tmState \in {"init", "commit", "abort", "hidden"}
          /\ pc \in [ProcSet -> {"RS", "TS", "TC", "F1", "TA", "F2",
                                 "BTS", "BTC", "BTA", "Done"}]

Consistency == \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                                       /\ rmState[rm2] = "committed"

NotCommitted == \A rm \in RM : rmState[rm] # "committed"

THEOREM Spec => [](TypeOK /\ Consistency)
=============================================================================