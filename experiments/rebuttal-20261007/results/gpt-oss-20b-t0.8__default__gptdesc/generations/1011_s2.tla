------------------------------ MODULE KeyValueStore ------------------------------
EXTENDS Naturals, TLC

CONSTANTS  Keys \* Set of keys
           Values \* Set of values
           MISSING \* Distinguished marker for missing entries

VARIABLES store, op, keyArg, valArg, retVal, ready, working

(**************************************************************************)
(* Types and Constants *)
(**************************************************************************)

Get     == "get"
Insert  == "insert"
Update  == "update"
Delete  == "delete"
None    == "none"

(**************************************************************************)
(* Initial State *)
(**************************************************************************)

Init ==
  /\ store = [k \in Keys |-> MISSING]
  /\ op   = None
  /\ keyArg = NULL
  /\ valArg = NULL
  /\ retVal = NULL
  /\ ready = TRUE
  /\ working = FALSE

(**************************************************************************)
(* Type Correctness Invariants *)
(**************************************************************************)

StoreTypeInv ==
  \A k \in Keys : store[k] \in Values \/ store[k] = MISSING

OpStateInv ==
  (ready /\ ~working /\ op = None) \/
  (~ready /\ working /\ op # None)

(**************************************************************************)
(* Request Actions *)
(**************************************************************************)

GetReq ==
  /\ ready
  /\ op'   = Get
  /\ keyArg'=CHOOSE k \in Keys : TRUE
  /\ valArg' = NULL
  /\ retVal' = NULL
  /\ ready'   = FALSE
  /\ working' = TRUE
  /\ UNCHANGED <<store>>

InsertReq ==
  /\ ready
  /\ op'    = Insert
  /\ keyArg'=CHOOSE k \in Keys : TRUE
  /\ valArg'=CHOOSE v \in Values : TRUE
  /\ retVal' = NULL
  /\ ready'   = FALSE
  /\ working' = TRUE
  /\ UNCHANGED <<store>>

UpdateReq ==
  /\ ready
  /\ op'    = Update
  /\ keyArg'=CHOOSE k \in Keys : TRUE
  /\ valArg'=CHOOSE v \in Values : TRUE
  /\ retVal' = NULL
  /\ ready'   = FALSE
  /\ working' = TRUE
  /\ UNCHANGED <<store>>

DeleteReq ==
  /\ ready
  /\ op'    = Delete
  /\ keyArg'=CHOOSE k \in Keys : TRUE
  /\ valArg' = NULL
  /\ retVal' = NULL
  /\ ready'   = FALSE
  /\ working' = TRUE
  /\ UNCHANGED <<store>>

(**************************************************************************)
(* Response Actions *)
(**************************************************************************)

GetResp ==
  /\ working
  /\ op = Get
  /\ retVal' = store[keyArg]
  /\ ready'   = TRUE
  /\ working' = FALSE
  /\ op'      = None
  /\ keyArg'  = NULL
  /\ valArg'  = NULL
  /\ UNCHANGED <<store>>

InsertResp ==
  /\ working
  /\ op = Insert
  /\ store'   = [store EXCEPT ![keyArg] = valArg]
  /\ retVal'  = "OK"
  /\ ready'   = TRUE
  /\ working' = FALSE
  /\ op'      = None
  /\ keyArg'  = NULL
  /\ valArg'  = NULL

UpdateResp ==
  /\ working
  /\ op = Update
  /\ store'   = [store EXCEPT ![keyArg] = valArg]
  /\ retVal'  = "OK"
  /\ ready'   = TRUE
  /\ working' = FALSE
  /\ op'      = None
  /\ keyArg'  = NULL
  /\ valArg'  = NULL

DeleteResp ==
  /\ working
  /\ op = Delete
  /\ store'   = [store EXCEPT ![keyArg] = MISSING]
  /\ retVal'  = "DELETED"
  /\ ready'   = TRUE
  /\ working' = FALSE
  /\ op'      = None
  /\ keyArg'  = NULL
  /\ valArg'  = NULL

(**************************************************************************)
(* Stuttering Action *)
(**************************************************************************)

Stutter ==
  /\ UNCHANGED <<store, op, keyArg, valArg, retVal, ready, working>>

(**************************************************************************)
(* Next-state Relation *)
(**************************************************************************)

Next ==
  \/ GetReq
  \/ InsertReq
  \/ UpdateReq
  \/ DeleteReq
  \/ GetResp
  \/ InsertResp
  /\ UpdateResp
  /\ DeleteResp
  \/ Stutter

(**************************************************************************)
(* Temporal Specification *)
(**************************************************************************)

Spec ==
  Init
  /\ [] (Next)
  /\ WF_0(DeleteReq) \* Weak fairness for delete requests

(**************************************************************************)
(* Safety Properties *)
(**************************************************************************)

Safety == StoreTypeInv /\ OpStateInv

=============================================================================