```tla
MODULE TerminationDetection

EXTENDS Integers, FiniteSets

CONSTANTS NumProcesses, MaxMessagesPerProcess

VARIABLES processes, messages, terminationDetected

Init ==
  /\ processes \in [1..NumProcesses -> {<<"active">>, <<"inactive">>}]
  /\ messages \in [1..NumProcesses -> Nat]
  /\ terminationDetected = FALSE

Next ==
  \/ \E p \in 1..NumProcesses :
    /\ processes[p] = <<"active">>
    /\ messages' = [messages EXCEPT ![p] = messages[p] + 1]
    /\ processes' = [processes EXCEPT ![p] = <<"inactive">>]
    /\ terminationDetected' = terminationDetected
    /\ UNCHANGED <<1..NumProcesses \ {p}>>
  \/ \E p, q \in 1..NumProcesses :
    /\ p # q
    /\ messages[p] > 0
    /\ processes[q] = <<"inactive">>
    /\ messages' = [messages EXCEPT ![p] = messages[p] - 1, ![q] = messages[q] + 1]
    /\ processes' = [processes EXCEPT ![q] = <<"active">>]
    /\ terminationDetected' = terminationDetected
    /\ UNCHANGED <<1..NumProcesses \ {p, q}>>
  \/ \E p \in 1..NumProcesses :
    /\ messages[p] > 0
    /\ processes[p] = <<"inactive">>
    /\ messages' = [messages EXCEPT ![p] = messages[p] - 1]
    /\ processes' = [processes EXCEPT ![p] = <<"active">>]
    /\ terminationDetected' = terminationDetected
    /\ UNCHANGED <<1..NumProcesses \ {p}>>
  \/ \E p \in 1..NumProcesses :
    /\ processes[p] = <<"active">>
    /\ messages[p] = 0
    /\ messages' = messages
    /\ processes' = [processes EXCEPT ![p] = <<"inactive">>]
    /\ terminationDetected' = terminationDetected
    /\ UNCHANGED <<1..NumProcesses \ {p}>>
  \/ (GlobalTermination ∧ ¬terminationDetected)
      /\ messages' = messages
      /\ processes' = processes
      /\ terminationDetected' = TRUE

Spec ==
  Init ∧ [][Next]_<<processes, messages, terminationDetected>>
  ∧ WF_<<processes, messages, terminationDetected>>(Next)

GlobalTermination ==
  /\ \A p \in 1..NumProcesses : processes[p] = <<"inactive">>
  /\ \A p \in 1..NumProcesses : messages[p] = 0

THEOREM Spec => []¬(terminationDetected ∧ ¬GlobalTermination)
THEOREM Spec => <>GlobalTermination => <>(GlobalTermination ∧ terminationDetected)

=============================================================================
```
Note: This TLA+ specification models the system as described, with processes and messages represented by variables. The `Next` action describes all possible transitions of the system, including sending and receiving messages, deactivating processes, and detecting termination. The `Spec` defines the complete behavior of the system, including the initial condition, the next-state relation, and fairness conditions. The `GlobalTermination` predicate represents the desired safety property, and the two THEOREM statements express the required liveness properties.