MODULE MultiNodeReadsAlt
EXTENDS MultiNodeReads

VARIABLES ledger, history

(* Alternative initial state with two pre‑committed transactions *)
AltInit == /\ ledger = [ "tx1" |-> "Committed", "tx2" |-> "Committed"]
          /\ history = << ["tx":"tx1","status":"Committed"],
                          ["tx":"tx2","status":"Committed"] >>

Init == AltInit

Next == MCNextMultiNodeReadsAction

Spec == Init /\ [][Next]_vars