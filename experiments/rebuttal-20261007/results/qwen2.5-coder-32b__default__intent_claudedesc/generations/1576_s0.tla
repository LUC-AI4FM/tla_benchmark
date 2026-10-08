------------------------------- MODULE ConcurrentQueue -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS N, Values, Processes

VARIABLES queue, results

Init == /\ queue = << >>
        /\ results = [p \in Processes |-> ""]
        
EnqueueBack ==
    /\ \E v \in Values : queue' = Append(queue, v)
    /\ UNCHANGED results
    
EnqueueFront ==
    /\ \E v \in Values : queue' = Prepend(v, queue)
    /\ UNCHANGED results

DequeueFront ==
    /\ queue # << >>
    /\ \E v \in Head(queue) : queue' = Tail(queue)
    /\ results' = [results EXCEPT ![p] = v]
    
DequeueBack ==
    /\ queue # << >>
    /\ \E v \in Last(queue) : queue' = Front(queue, Len(queue)-1)
    /\ results' = [results EXCEPT ![p] = v]

ReportFull ==
    /\ Len(queue) >= N
    /\ results' = [results EXCEPT ![p] = "full"]
    /\ UNCHANGED queue

ReportEmpty ==
    /\ queue = << >>
    /\ results' = [results EXCEPT ![p] = "empty"]
    /\ UNCHANGED queue
    
ClearResult ==
    /\ results' = [results EXCEPT ![p] = ""]
    /\ UNCHANGED queue

Next ==
    \E p \in Processes : \/ EnqueueBack
                           \/ EnqueueFront
                           \/ DequeueFront
                           \/ DequeueBack
                           \/ ReportFull
                           \/ ReportEmpty
                           \/ ClearResult

Spec == Init /\ [][Next]_<<p \in Processes >> /\ WF_[[Next]]_<<p \in Processes >>

QueueLengthBound == Len(queue) <= N

=============================================================================