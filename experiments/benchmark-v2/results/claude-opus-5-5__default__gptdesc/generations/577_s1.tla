---------------------------- MODULE MCMultiNodeReadsAlt ----------------------------
(***************************************************************************)
(* Alternative initial state for the multi-node reads model.               *)
(*                                                                         *)
(* This module extends the base model MCMultiNodeReads. The base module    *)
(* (and the modules it extends) already declare all CONSTANTS and          *)
(* VARIABLES, including ledgerBranches, history and the tuple vars, and    *)
(* define the next-state action MCNextMultiNodeReadsAction. They are not   *)
(* redeclared here, because redeclaring them would be a SANY error.        *)
(*                                                                         *)
(* All safety invariants and liveness properties are inherited from the    *)
(* base specification. The description adds no new properties and no       *)
(* fairness conditions.                                                    *)
(***************************************************************************)
EXTENDS MCMultiNodeReads

\* Alternative initial state where two transactions are already committed
InitAlt ==
    /\ ledgerBranches = <<
        << [view |-> 1, tx |-> 0],
           [view |-> 1, tx |-> 1] >>
       >>
    /\ history = <<
        [type |-> RwTxRequest,  tx |-> 0],
        [type |-> RwTxResponse, tx |-> 0, observed |-> <<0>>,    tx_id |-> <<1, 1>>],
        [type |-> RwTxRequest,  tx |-> 1],
        [type |-> RwTxResponse, tx |-> 1, observed |-> <<0, 1>>, tx_id |-> <<1, 2>>],
        [type |-> TxStatusReceived, tx_id |-> <<1, 1>>, status |-> CommittedStatus],
        [type |-> TxStatusReceived, tx_id |-> <<1, 2>>, status |-> CommittedStatus]
       >>

\* Next-state relation imported from the base multi-node reads model
NextAlt == MCNextMultiNodeReadsAction

\* Temporal specification starting from the alternative initial state
SpecAlt == InitAlt /\ [][MCNextMultiNodeReadsAction]_vars

=============================================================================