---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes
VARIABLES messages, active, terminated

messages == [p \in Processes |-> {}]
active == [p \in Processes |-> TRUE]
terminated == FALSE

TypeInvariant ==
  /\ messages \in [Processes -> SUBSET Int]
  /\ active \in [Processes -> BOOLEAN]
  /\ terminated \in BOOLEAN

Termination ==
  /\ \A p \in Processes : ~active[p]
  /\ \A p \in Processes : messages[p] = {}

DetectorSafety ==
  terminated => Termination

Liveness ==
  <>[]Termination => <>terminated

Quiescence ==
  []<>(Termination => []Termination)

Send(p, q) == 
  /\ p \in Processes
  /\ q \in Processes
  /\ active[p]
  /\ messages' = [messages EXCEPT ![p] = {1} \cup messages[p]]
  /\ active' = active
  /\ terminated' = terminated

Receive(p, q) == 
  /\ p \in Processes
  /\ q \in Processes
  /\ messages[q] # {}
  /\ messages' = [messages EXCEPT ![q] = {}]
  /\ active' = [active EXCEPT ![p] = TRUE]
  /\ terminated' = terminated

Deactivate(p) == 
  /\ p \in Processes
  /\ active[p]
  /\ messages[p] = {}
  /\ messages' = messages
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ terminated' = terminated

Detect ==
  /\ Termination
  /\ terminated' = TRUE
  /\ messages' = messages
  /\ active' = active

Next == 
  \E p, q \in Processes : 
    (Send(p, q) \/ Receive(p, q) \/ Deactivate(p) \/ Detect)

Spec == 
  /\ TypeInvariant
  /\ []TypeInvariant
  /\ (active = [p \in Processes |-> TRUE]) /\ (messages = [p \in Processes |-> {}])
  /\ []<>(Next)
  /\ WF_vars(<<Send, Receive, Deactivate, Detect>>_vars)

THEOREM Spec => []DetectorSafety
THEOREM Spec => Liveness
THEOREM Spec => Quiescence

=============================================================================