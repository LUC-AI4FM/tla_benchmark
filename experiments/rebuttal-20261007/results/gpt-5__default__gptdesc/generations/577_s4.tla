----------------------------- MODULE AltInitMultiNodeReads -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  Alternative initial state for the multi-node reads model.
  Initializes ledger branches and history so that two transactions are already committed.
*)

CONSTANTS
  BranchIds,   \* Domain of branch identifiers in the ledger
  Tx1, Tx2,    \* Two distinct transaction identifiers, pre-committed in the initial history
  OkResp1,     \* Pre-populated response corresponding to Tx1
  OkResp2      \* Pre-populated response corresponding to Tx2
  

VARIABLES
  dummy        \* Local dummy variable to satisfy the VARIABLES declaration in this module

(*
  Import the base multi-node reads specification, which provides:
    - the action MCNextMultiNodeReadsAction
    - the state vector vars
    - the state variables, including History and LedgerBranches (referenced below)
*)
INSTANCE MC_MultiNodeReads AS Base

TwoCommittedHistory ==
  << [ tx        |-> Tx1,
       resp      |-> OkResp1,
       committed |-> TRUE ],
     [ tx        |-> Tx2,
       resp      |-> OkResp2,
       committed |-> TRUE ] >>

InitAlt ==
  /\ Tx1 # Tx2
  /\ Base!History = TwoCommittedHistory
  /\ Base!LedgerBranches = [ b \in BranchIds |-> << Tx1, Tx2 >> ]
  /\ dummy = 0

Init == InitAlt

Next == Base!MCNextMultiNodeReadsAction

Spec == Init /\ [][Next]_(Base!vars)

=======================================================================================