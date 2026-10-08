---- MODULE FischerTimedMutualExclusion ----

EXTENDS Integers, Sequences, TLC

CONSTANTS N, Delta, Epsilon, Infinity

VARIABLES 
    \* Per-process timers
    timer,
    \* Process priorities
    priority,
    \* Process requests to enter critical section
    request,
    \* The process currently in the critical section (if any)
    in_critical_section

Init == 
    /\ timer = <<Infinity \: N>>
    /\ priority = <<1 \: N>>
    /\ request = <<FALSE \: N>>
    /\ in_critical_section = FALSE

Next == \/ \E i \in 1..N :
            /\ ~request[i]
            /\ \A j \in 1..N : ~request[j] \/ priority[j] < priority[i] 
                                               \/ (priority[j] = priority[i] /\ j <= i)
            /\ request' = [request EXCEPT ![i] = TRUE]
               /\ timer' = [timer EXCEPT ![i] = timer[i]]
               /\ priority' = priority
               /\ in_critical_section' = FALSE
         \\/ \E i \in 1..N :
            /\ request[i]
            /\ \A j \in 1..N : ~request[j] \/ (priority[j] < priority[i])
                                               \/ (priority[j] = priority[i] /\ j <= i)
            /\ in_critical_section' = i
               /\ request' = [request EXCEPT ![i] = FALSE]
               /\ timer' = timer
               /\ priority' = priority
         \\/ \E i \in 1..N :
            /\ request[i]
            /\ \A j \in {j \in 1..N : j # i} : ~request[j] \/ (priority[j] < priority[i])
                                                             \/ (priority[j] = priority[i] /\ j <= i)
            /\ in_critical_section' = FALSE
               /\ request' = [request EXCEPT ![i] = FALSE]
               /\ timer' = [timer EXCEPT ![i] = Infinity]
               /\ priority' = priority
         \\/ \E i \in 1..N :
            /\ ~request[i]
            /\ \A j \in {j \in 1..N : j # i} : ~request[j] \/ (priority[j] < priority[i])
                                                             \/ (priority[j] = priority[i] /\ j <= i)
            /\ in_critical_section' = FALSE
               /\ request' = request
               /\ timer' = [timer EXCEPT ![i] = Infinity]
               /\ priority' = priority
         \\/ \E i \in 1..N :
            /\ ~request[i]
            /\ timer[i] > Epsilon
            /\ timer' = [timer EXCEPT ![i] = timer[i] - Delta]
               /\ request' = request
               /\ priority' = priority
               /\ in_critical_section' = FALSE

Spec == 
    Init /\ [][Next]_<<request, priority, timer, in_critical_section>> 

\* Mutual exclusion invariant: At most one process can be in the critical section at any time.
MutualExclusion == \/ in_critical_section = FALSE
                    \/ \E i \in 1..N : in_critical_section = i

\* Liveness property: Some process is infinitely often in the critical section.
LivenessProperty == <>[] <>(\E i \in 1..N : in_critical_section = i)

Inv == MutualExclusion /\ \/ in_critical_section = FALSE
                          \/ \A j \in 1..N : request[j] => timer[j] <= Infinity

Fairness ==
    WF_next(\A i \in 1..N : pc[i] = "request_entry")
    /\ SF_\E(\E i \in 1..N : pc[i] = "critical_section")

\* TLC-based check of named state counts
StateConstraints == 
    /\ \A i \in 1..N : timer[i] >= 0 \/ in_critical_section = FALSE

====