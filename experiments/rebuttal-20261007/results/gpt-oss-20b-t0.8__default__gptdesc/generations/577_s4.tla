MODULE MultiNodeReadsAltInit
EXTENDS MultiNodeReadsModel

VARIABLES vars

(* Alternative initial state predicate *)
InitAlternative ==
    /\ BaseInit
    /\ vars = [ ledgerBranches |-> <<>>, 
                history |-> << [txid |-> 1, status |-> "Committed", response |-> "ok"],
                                [txid |-> 2, status |-> "Committed", response |-> "ok"] >> ]

(* Stuttering form of the next action *)
StutteredAction ==
    MCNextMultiNodeReadsAction \/ vars' = vars

Spec == InitAlternative /\ [] (StutteredAction)