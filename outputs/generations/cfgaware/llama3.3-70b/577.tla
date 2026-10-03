--------------------------- MODULE MCSpecMultiNodeReadsAlt ---------------------------
EXTENDS Integers, MCBaseSpecMultiNodeReads

VARIABLES ledger, history, response, committed

InitAlternative == (* Initial state with two transactions already committed *)
                  /\ ledger = <<1, 2>>
                  /\ history = <<[response |-> <<>>, committed |-> FALSE],
                             [response |-> <<>>, committed |-> FALSE]>>
                  /\ response = <<>>
                  /\ committed = FALSE

MCNextMultiNodeReadsAction == (* Action definition imported from MCBaseSpecMultiNodeReads *)
                             MCBaseSpecMultiNodeReads!MCNextMultiNodeReadsAction

MCSpecMultiNodeReadsAlt == InitAlternative ∧ [][MCNextMultiNodeReadsAction]_vars
====================================================================================