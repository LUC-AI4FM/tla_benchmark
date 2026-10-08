EXTENDS MCMultiNodeReads

(***************************************************************************)
(*  Alternative initial state for multi‑node read verification            *)
(***************************************************************************)

InitAlt ==
  /\ Init
  /\ (* Two transactions are already committed in the ledger and history.
       The exact structure of Ledger and History depends on the parent
       module.  Here we provide a minimal concrete instance that satisfies
       the type constraints expected by MCMultiNodeReads. *)
  LET
    tx1 == [id -> 1, view -> 1, status -> "committed"]
    tx2 == [id -> 2, view -> 2, status -> "committed"]
  IN
    /\ Ledger = [1 |-> [branch -> 1], 2 |-> [branch -> 2]]
    /\ History = <<tx1, tx2>>

(***************************************************************************)
(*  Specification that pairs the alternative initial state with the      *)
(*  original next‑state relation.                                        *)
(***************************************************************************)

MCSpecMultiNodeReadsAlt ==
  /\ InitAlt
  /\ [][MCNextMultiNodeReadsAction]_<<Ledger, History>>

