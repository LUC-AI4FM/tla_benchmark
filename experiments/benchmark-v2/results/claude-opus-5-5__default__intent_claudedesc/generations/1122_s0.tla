---------------------------- MODULE TwoPCwithBTM ----------------------------
(***************************************************************************)
(* Two-phase commit with a primary transaction manager (TM) and a backup   *)
(* transaction manager (BTM).  Resource managers (RMs) and the primary TM  *)
(* may optionally fail, as set by the RMMAYFAIL and TMMAYFAIL constants.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS RM,          \* the set of resource managers
          RMMAYFAIL,   \* TRUE iff resource managers may fail
          TMMAYFAIL    \* TRUE iff the primary TM may fail

ASSUME RMMAYFAIL \in BOOLEAN
ASSUME TMMAYFAIL \in BOOLEAN
ASSUME RM \cap {0, 10} = {}

VARIABLES rmState, tmState, btmState, pc

vars == << rmState, tmState, btmState, pc >>

TMId  == 0
BTMId == 10

ProcSet == RM \cup {TMId} \cup {BTMId}

RMStates  == {"working", "prepared", "committed", "aborted", "failed"}
TMStates  == {"init", "commit", "abort", "hidden"}
BTMStates == {"init", "commit", "abort"}
PCs       == {"RS", "TS", "TC", "TA", "F1", "F2", "BTS", "BTC", "BTA", "Done"}

(***************************************************************************)
(* Decision predicates used by the TM and the BTM                          *)
(***************************************************************************)
canCommit ==
    \/ \A rmc \in RM : rmState[rmc] = "prepared"
    \/ \E rm \in RM : rmState[rm] = "committed"

canAbort ==
    /\ \E rm \in RM : rmState[rm] \in {"aborted", "failed"}
    /\ ~\E rmc \in RM : rmState[rmc] = "committed"

-----------------------------------------------------------------------------
Init ==
    /\ rmState  = [rm \in RM |-> "working"]
    /\ tmState  = "init"
    /\ btmState = "init"
    /\ pc = [self \in ProcSet |->
               CASE self \in RM    -> "RS"
                 [] self = TMId    -> "TS"
                 [] self = BTMId   -> "BTS"]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Resource manager                                                        *)
(***************************************************************************)
Prepare(p) ==
    /\ rmState[p] = "working"
    /\ rmState' = [rmState EXCEPT ![p] = "prepared"]

DecideCommit(p) ==
    /\ tmState = "commit" \/ btmState = "commit"
    /\ rmState' = [rmState EXCEPT ![p] = "committed"]

DecideAbort(p) ==
    /\ rmState[p] = "working" \/ tmState = "abort" \/ btmState = "abort"
    /\ rmState' = [rmState EXCEPT ![p] = "aborted"]

Fail(p) ==
    /\ RMMAYFAIL
    /\ rmState' = [rmState EXCEPT ![p] = "failed"]

RS(self) ==
    /\ pc[self] = "RS"
    /\ IF rmState[self] \in {"working", "prepared"}
          THEN /\ \/ Prepare(self)
                  \/ DecideCommit(self)
                  \/ DecideAbort(self)
                  \/ Fail(self)
               /\ pc' = pc
          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED rmState
    /\ UNCHANGED << tmState, btmState >>

RManager(self) == RS(self)

(***************************************************************************)
(* Primary transaction manager                                             *)
(***************************************************************************)
TS ==
    /\ pc[TMId] = "TS"
    /\ \/ /\ canCommit
          /\ pc' = [pc EXCEPT ![TMId] = "TC"]
       \/ /\ canAbort
          /\ pc' = [pc EXCEPT ![TMId] = "TA"]
    /\ UNCHANGED << rmState, tmState, btmState >>

TC ==
    /\ pc[TMId] = "TC"
    /\ tmState' = "commit"
    /\ pc' = [pc EXCEPT ![TMId] = "F1"]
    /\ UNCHANGED << rmState, btmState >>

F1 ==
    /\ pc[TMId] = "F1"
    /\ IF TMMAYFAIL THEN tmState' = "hidden" ELSE UNCHANGED tmState
    /\ pc' = [pc EXCEPT ![TMId] = "Done"]
    /\ UNCHANGED << rmState, btmState >>

TA ==
    /\ pc[TMId] = "TA"
    /\ tmState' = "abort"
    /\ pc' = [pc EXCEPT ![TMId] = "F2"]
    /\ UNCHANGED << rmState, btmState >>

F2 ==
    /\ pc[TMId] = "F2"
    /\ IF TMMAYFAIL THEN tmState' = "hidden" ELSE UNCHANGED tmState
    /\ pc' = [pc EXCEPT ![TMId] = "Done"]
    /\ UNCHANGED << rmState, btmState >>

TManager == TS \/ TC \/ F1 \/ TA \/ F2

(***************************************************************************)
(* Backup transaction manager                                              *)
(***************************************************************************)
BTS ==
    /\ pc[BTMId] = "BTS"
    /\ \/ /\ canCommit /\ tmState = "hidden"
          /\ pc' = [pc EXCEPT ![BTMId] = "BTC"]
       \/ /\ canAbort /\ tmState = "hidden"
          /\ pc' = [pc EXCEPT ![BTMId] = "BTA"]
    /\ UNCHANGED << rmState, tmState, btmState >>

BTC ==
    /\ pc[BTMId] = "BTC"
    /\ btmState' = "commit"
    /\ pc' = [pc EXCEPT ![BTMId] = "Done"]
    /\ UNCHANGED << rmState, tmState >>

BTA ==
    /\ pc[BTMId] = "BTA"
    /\ btmState' = "abort"
    /\ pc' = [pc EXCEPT ![BTMId] = "Done"]
    /\ UNCHANGED << rmState, tmState >>

BTManager == BTS \/ BTC \/ BTA

-----------------------------------------------------------------------------
(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A self \in ProcSet : pc[self] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ TManager
    \/ BTManager
    \/ (\E self \in RM : RManager(self))
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in RM : WF_vars(RManager(self))
    /\ WF_vars(TManager)
    /\ WF_vars(BTManager)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ rmState \in [RM -> RMStates]
    /\ tmState \in TMStates
    /\ btmState \in BTMStates
    /\ pc \in [ProcSet -> PCs]

Consistency ==
    \A rm1, rm2 \in RM :
        ~ /\ rmState[rm1] = "aborted"
          /\ rmState[rm2] = "committed"

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

THEOREM Spec => [](TypeOK /\ Consistency)
=============================================================================