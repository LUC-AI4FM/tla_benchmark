```
MODULE AlternativeInitMultiNodeReads
EXTENDS BaseMultiNodeReadsSpec

CONSTANTS NodeSet, TxnSet
VARIABLES ledger, history, response, committed

Init ==
  /\ ledger = [n \in NodeSet |-> <<>>]
  /\ history = <<
    [TxnSet |->
      [n \in NodeSet |-> 
        IF n = "Node1" THEN << "Txn1", TRUE >> 
        ELSEIF n = "Node2" THEN << "Txn2", TRUE >> 
        ELSE << "", FALSE >>
      ]
    ]
  >>
  /\ response = [n \in NodeSet |-> [t \in TxnSet |-> ""]]
  /\ committed = [n \in NodeSet |-> [t \in TxnSet |-> FALSE]]

Next == [](MCNextMultiNodeReadsAction)_vars

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Init
```
Note: I assume that the `BaseMultiNodeReadsSpec` module is already defined elsewhere and that it includes the definition of `MCNextMultiNodeReadsAction`. Also, I used a simple example for the initialization of `history`, you should adjust it according to your actual requirements.