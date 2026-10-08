------------------------------ MODULE NBACAlgorithm ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Procs,                    \* Set of processes
    MsgPool                   \* Set of all possible messages

VARIABLES 
    votes,                    \* Votes from each process (YES/NO/UNDECIDED)
    outbox,                   \* Outbox for each process to send messages
    inbox,                    \* Inbox for each process to receive messages
    failed,                   \* Set of processes that have crashed
    fd                         \* Failure detector output

Init == 
    /\ votes = [p \in Procs |-> "UNDECIDED"]
    /\ outbox = [p \in Procs |-> {}]
    /\ inbox = [p \in Procs |-> {}]
    /\ failed = {}
    /\ fd = {}

Next == 
    \/ /\ E \in SUBSET Procs
       /\ UNCHANGED votes
       /\ \A p \in E : outbox' = [outbox EXCEPT ![p] = {}]
       /\ inbox' = [inbox EXCEPT !["p] = inbox["p] \cup outbox[p] : p \notin E]
       /\ failed' = Union({failed, {p} : p \in E})
       /\ fd' = fd
    \/ /\ p \in Procs
       /\ ~(p \in failed)
       /\ (fd'[p] \in SUBSET Procs) 
       /\ votes' = [votes EXCEPT ![p] = IF \A q \notin fd[p] : votes[q] = "YES" THEN "YES"
                                  ELSE IF \A q \notin fd[p] : votes[q] = "NO" THEN "NO"
                                  ELSE votes[p]]
       /\ outbox'[p] = {<<q, votes'[p]>> : q \in (Procs \ {p})}
       /\ inbox' = [inbox EXCEPT !["p] = inbox["p]]
       /\ failed' = failed
       /\ fd' = [fd EXCEPT ![p] = fd'[p]]

Spec == 
    Init /\ [][Next]_<<votes, outbox, inbox, failed, fd>> /\ WF_<<votes, outbox, inbox, failed, fd>>(Next)

\* Type invariants
TypeInvariant ==
    /\ votes \in [Procs -> {"YES", "NO", "UNDECIDED"}]
    /\ outbox \in [Procs -> SUBSET MsgPool]
    /\ inbox \in [Procs -> SUBSET MsgPool]
    /\ failed \in SUBSET Procs
    /\ fd \in [Procs -> SUBSET Procs]

\* Validity condition
Validity ==
    \/ \E p \in Procs : votes[p] = "YES" => \A q \notin failed : votes[q] = "YES"
    \/ \E p \in Procs : votes[p] = "NO"  => \A q \notin failed : votes[q] = "NO"

\* Liveness property
Liveness ==
    <>(\E p \in Procs : votes[p] = "YES") \/ <>(\E p \in Procs : votes[p] = "NO")

THEOREM Spec => []TypeInvariant

THEOREM Spec => []Validity

THEOREM Spec => <>Liveness

=============================================================================