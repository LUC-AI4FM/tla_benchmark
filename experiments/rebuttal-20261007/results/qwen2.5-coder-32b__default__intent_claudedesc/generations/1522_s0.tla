------------------------------- MODULE HuangTerminationDetection -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Procs,  \* Set of processes
    Leader  \* Designated leader process

VARIABLES 
    weights,  \* Function from processes to their local weights
    messages  \* Multiset of messages in transit; each message is a tuple (sender, receiver, weight)

Init == /\ weights = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
        /\ messages = << >>

Next ==
    \/ \E sender \in Procs, receiver \in Procs \ {sender}, w \in Nat :
         /\ weights[sender] > 0
         /\ messages' = Append(messages, <<sender, receiver, w / 2>>)
         /\ weights' = [weights EXCEPT ![sender] = weights[sender] - w / 2]
    \/ \E sender \in Procs, receiver \in Procs \ {sender}, w \in Nat :
         /\ messages /= << >>
         /\ Head(messages) = <<sender, receiver, w>>
         /\ messages' = Tail(messages)
         /\ weights' = [weights EXCEPT ![receiver] = weights[receiver] + w]
    \/ \E p \in Procs \ {Leader} :
         /\ weights[p] > 0
         /\ messages' = Append(messages, <<p, Leader, weights[p]>>)
         /\ weights' = [weights EXCEPT ![p] = 0]
    \/ /\ weights[Leader] < 1
       /\ messages /= << >>
       /\ \E p \in Procs \ {Leader}, w \in Nat :
            /\ Head(messages) = <<p, Leader, w>>
            /\ messages' = Tail(messages)
            /\ weights' = [weights EXCEPT ![Leader] = weights[Leader] + w]

Spec ==
    /\ Init
    /\ [][Next]_<<messages, weights>>

TerminationDetected ==
    /\ weights[Leader] = 1
    /\ \A p \in Procs \ {Leader} : weights[p] = 0
    /\ messages = << >>

SafetyInvariant ==
    \/ ~ TerminationDetected
    \/ /\ TerminationDetected
       /\ [](TerminationDetected)

LivenessProperty ==
    <>(TerminationDetected)

Fairness ==
    WF_next(Next)

THEOREM Spec => []SafetyInvariant

THEOREM Spec /\ Fairness => <>LivenessProperty

=================================================================================================