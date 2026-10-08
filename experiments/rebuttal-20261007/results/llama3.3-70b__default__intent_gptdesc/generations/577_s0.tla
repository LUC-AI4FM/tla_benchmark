```
MODULE DistributedLedger
EXTENDS Integers, Sequences, TLC

CONSTANTS Nodes, Transactions, InitialCommits
VARIABLES nodeState, transactionStatus, readResults

Init ==
  /\ nodeState = [n \in Nodes |-> {}]
  /\ transactionStatus = [t \in Transactions |-> "pending"]
  /\ readResults = [n \in Nodes |-> {}]

Next ==
  /\ IF \E n \in Nodes : 
        /\ \E t \in Transactions :
            /\ transactionStatus[t] = "pending"
            /\ nodeState' = [nodeState EXCEPT ![n] = Append(nodeState[n], t)]
            /\ transactionStatus' = [transactionStatus EXCEPT ![t] = "proposed"]
            /\ readResults' = readResults
        ELSE 
        /\ \E n \in Nodes : 
            /\ \E t \in Transactions :
                /\ transactionStatus[t] = "proposed"
                /\ nodeState' = nodeState
                /\ transactionStatus' = [transactionStatus EXCEPT ![t] = "committed"]
                /\ readResults' = [readResults EXCEPT ![n] = Append(readResults[n], t)]
        ELSE 
        /\ \E n \in Nodes : 
            /\ readResults' = [readResults EXCEPT ![n] = {t \in nodeState[n] : transactionStatus[t] = "committed"}]
            /\ nodeState' = nodeState
            /\ transactionStatus' = transactionStatus
  /\ UNCHANGED <<nodeState, transactionStatus, readResults>>

Spec ==
  /\ Init
  /\ [][Next]_<<nodeState, transactionStatus, readResults>>
  /\ WF_vars(<<nodeState, transactionStatus, readResults>>)

SafetyInvariant1 == 
  \A n \in Nodes, t \in Transactions : 
    (transactionStatus[t] = "committed") => (t \in nodeState[n])

SafetyInvariant2 == 
  \A n \in Nodes, r1 \in readResults[n], r2 \in readResults[n] :
    (r1 /= r2) => ((r1 << r2) \/ (r2 << r1))

LivenessProperty ==
  \A t \in Transactions : 
    <>[]<>(transactionStatus[t] = "committed")

MonotonicVisibility == 
  \A n \in Nodes, r1 \in readResults[n], r2 \in readResults[n] :
    (r1 /= r2) => ((r1 << r2) \/ (r2 << r1))

ConsistencyAcrossNodes == 
  \A t \in Transactions : 
    <>[]<>(\A n \in Nodes : transactionStatus[t] = "committed")

THEOREM Spec => []SafetyInvariant1
THEOREM Spec => []SafetyInvariant2
THEOREM Spec => LivenessProperty
THEOREM Spec => MonotonicVisibility
THEOREM Spec => ConsistencyAcrossNodes

=============================================================================
```
Note: The `<<` and `>>` are used to denote the tuple of variables, which is a common convention in TLA+. Also, this specification uses the `WF_vars` operator to specify weak fairness for the variables. This ensures that every possible step will eventually be taken if it is continuously enabled. 

Please note that you may need to adjust the model according to your specific requirements and also make sure that the model is correct with respect to the problem description.