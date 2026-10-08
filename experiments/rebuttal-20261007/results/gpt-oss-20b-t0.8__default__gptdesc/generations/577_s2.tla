--------------------------- MODULE AlternativeInitialState ----------------------------
EXTENDS Naturals, Sequences, TLC, MultiNodeReadsBase

VARIABLES vars

(* Initial state where two transactions are already committed *)
AltInit ==
  /\ vars = [ ledgerBranches |-> <<0,0>>,
              history |-> << 
                    [ txid |-> "t1", status |-> "committed" ],
                    [ txid |-> "t2", status |-> "committed" ] >> ]

Init == AltInit

Next == MCNextMultiNodeReadsAction

Spec == Init /\ [][Next]_{vars}

=============================================================================