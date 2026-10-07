MODULE MCSpecMultiNodeReadsAlt
EXTENDS MCMultiNodeReads

CONSTANTS HistoryLimit = 11, ViewLimit = 3

VARIABLES Ledger, History

(* Alternative initial state with two committed transactions *)
InitAlt ==
    /\ Ledger   = [1 -> 1, 2 -> 2]
    /\ History  = [tx1 |-> [req -> "r1", resp -> "c1", status -> Committed],
                   tx2 |-> [req -> "r2", resp -> "c2", status -> Committed]]
    /\ TRUE

Next == MCNextMultiNodeReadsAction

Spec == InitAlt /\ [][Next]_(<<Ledger,History>>)

===============================================================================