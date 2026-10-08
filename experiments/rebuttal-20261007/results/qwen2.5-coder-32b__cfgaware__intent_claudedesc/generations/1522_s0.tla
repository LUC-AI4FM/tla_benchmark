------------------------------- MODULE HuangTerminationDetection -------------------------------

CONSTANTS 
    Procs,          \* The set of all processes
    Leader          \* The designated leader process

VARIABLES 
    weights,        \* A function mapping each process to its current weight
    messages        \* A function mapping each process to a list of received messages (each message is a pair <sender, weight>)

ASSUME Procs \subseteq Nat /\ Leader \in Procs /\ Cardinality(Procs) > 1

CONSTANTS InitWeight \* The initial unit of weight held by the leader
ASSUME InitWeight = 1.0

\* Initial predicate: only the leader is active with full weight, others are idle with zero weight
Init == 
    /\ weights = [p \in Procs |-> IF p = Leader THEN InitWeight ELSE 0.0]
    /\ messages = [p \in Procs |-> <<>>]

\* A process sends half of its weight to another process
Send(p, q) ==
    /\ p \in Procs \ {Leader}
    /\ q \in Procs \ {p}
    /\ weights[p] > 0.0
    /\ LET halfWeight == weights[p] / 2.0 IN
        \/ /\ weights' = [weights EXCEPT ![p] = weights[p] - halfWeight, ![q] = weights[q] + halfWeight]
           /\ messages' = [messages EXCEPT ![q] = Append(messages[q], <<p, halfWeight>>)]
        \/ /\ weights' = [weights EXCEPT ![p] = 0.0]
           /\ messages' = [messages EXCEPT ![q] = Append(messages[q], <<p, weights[p]>>)]

\* A non-leader process becomes active by receiving a message
Receive(p) ==
    /\ p \in Procs \ {Leader}
    /\ Len(messages[p]) > 0
    /\ LET msg == Head(messages[p])
         sender == fst(msg)
         receivedWeight == snd(msg) IN
        \/ /\ weights' = [weights EXCEPT ![p] = weights[p] + receivedWeight]
           /\ messages' = [messages EXCEPT ![p] = Tail(messages[p])]
        \/ /\ weights' = [weights EXCEPT ![p] = 0.0]
           /\ messages' = [messages EXCEPT ![p] = <<>>]

\* The leader receives returned weight from a non-leader process
LeaderReceive ==
    /\ Len(messages[Leader]) > 0
    /\ LET msg == Head(messages[Leader])
         sender == fst(msg)
         receivedWeight == snd(msg) IN
        \/ /\ weights' = [weights EXCEPT ![Leader] = weights[Leader] + receivedWeight]
           /\ messages' = [messages EXCEPT ![Leader] = Tail(messages[Leader])]

\* The leader becomes idle if it holds the entire unit of weight and no messages are in transit
LeaderIdle ==
    /\ weights[Leader] = InitWeight
    /\ \A p \in Procs : Len(messages[p]) = 0
    /\ \A p \in Procs \ {Leader} : weights[p] = 0.0

\* A non-leader process becomes idle if it has no messages and its weight is zero
ProcessIdle(p) ==
    /\ p \in Procs \ {Leader}
    /\ weights[p] = 0.0
    /\ Len(messages[p]) = 0

\* The system is in a stable termination state
Termination ==
    /\ LeaderIdle
    /\ \A p \in Procs \ {Leader} : ProcessIdle(p)

Next == 
    \/ \E p, q \in Procs : Send(p, q)
    \/ \E p \in Procs \ {Leader} : Receive(p)
    \/ LeaderReceive

Spec == Init /\ [][Next]_<<weights, messages>>

\* The total weight in the system is always 1
TotalWeight ==
    SUM {weights[p] : p \in Procs} + SUM {SUM {snd(msg) : msg \in messages[p]} : p \in Procs} = InitWeight

THEOREM Spec => []TotalWeight

=============================================================================