------------------------------- MODULE AsyncCommit --------------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    Procs \* The set of processes
    Votes  \* The possible votes: {"YES", "NO"}

VARIABLES 
    vote       \* vote[p] is the vote of process p
    suspected  \* suspected[p] is TRUE if p is suspected, else FALSE
    sent       \* sent[p][q] is the set of messages sent from p to q
    received   \* received[q][p] is the set of messages received by q from p
    state      \* state[p] is either "VOTING", "ABORTED", or "COMMITTED"

Init == 
    /\ vote \in [Procs -> Votes]
    /\ suspected \in [Procs -> {FALSE}]
    /\ sent \in [Procs -> [Procs -> {}]]
    /\ received \in [Procs -> [Procs -> {}]]
    /\ state \in [Procs -> {"VOTING"}]

Next ==
    \/ \E p \in Procs : \* Process p sends its vote
        /\ ~suspected[p]
        /\ sent' = [sent EXCEPT ![p] = [q \in (Procs \ {p}) -> sent[p][q] \cup {vote[p]}]]
    \/ \E p, q \in Procs : \* Process q receives a message from p
        /\ ~suspected[q]
        /\ received' = [received EXCEPT ![q][p] = received[q][p] \cup sent[p][q]]
    \/ \E p \in Procs : \* Process p aborts due to suspicion
        /\ suspected[p]
        /\ state' = [state EXCEPT ![p] = "ABORTED"]
    \/ \E q \in Procs : \* Process q commits if all received votes are the same
        /\ ~suspected[q]
        /\ ~(\E p1, p2 \in (Procs \ {q}) : 
            (received[q][p1] /= {} /\ received[q][p2] /= {}) 
            /\ (CHOOSE v1 \in received[q][p1] : TRUE) # (CHOOSE v2 \in received[q][p2] : TRUE))
        /\ state' = [state EXCEPT ![q] = "COMMITTED"]

Spec == Init /\ [][Next]_<<Procs>>

TypeInvariant ==
    /\ vote \in [Procs -> Votes]
    /\ suspected \in [Procs -> {FALSE, TRUE}]
    /\ sent \in [Procs -> [Procs -> SUBSET Votes]]
    /\ received \in [Procs -> [Procs -> SUBSET Votes]]
    /\ state \in [Procs -> {"VOTING", "ABORTED", "COMMITTED"}]

Agreement ==
    \/ (\A p \in Procs : state[p] = "ABORTED")
    \/ (\E v \in Votes : \A q \in Procs : state[q] = "COMMITTED" => vote[q] = v)

AbortValidity ==
    \A p \in Procs : suspected[p] => state[p] = "ABORTED"

CommitValidity ==
    \A q \in Procs : state[q] = "COMMITTED" => 
        (\A p \in (Procs \ {q}) : received[q][p] /= {} /\ (CHOOSE v \in received[q][p] : TRUE) = vote[p])

Termination ==
    []<>(\A p \in Procs : state[p] \notin {"VOTING"})

EventualCommit ==
    <>(\E q \in Procs : state[q] = "COMMITTED")

Invariant ==
    TypeInvariant /\ Agreement /\ AbortValidity /\ CommitValidity

WF ==
    WF_nonstuttering(ProcessActions)

ProcessActions ==
    {p \in Procs | ~suspected[p]}

Liveness ==
    Termination /\ EventualCommit

THEOREM Spec => []Invariant /\ <>Liveness

=============================================================================