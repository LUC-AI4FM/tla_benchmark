------------------------------- MODULE ResourceAllocator -------------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS 
    Clients, Resources

VARIABLES 
    heldResources, requests, schedule

Init == /\ heldResources = [c \in Clients |-> {}]
        /\ requests = [c \in Clients |-> {}]
        /\ schedule = <<>>

Next ==
    \/ \E c \in Clients, r \in Requests[c] :
        /\ r \notin heldResources[c]
        /\ \A s \in SUBSEQ(schedule) : r \notin UNION {heldResources[s]}
        /\ requests' = [requests EXCEPT ![c] = requests[c] \ {r}]
        /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup {r}]
        /\ schedule' = schedule
    \/ \E c \in Clients, r \in heldResources[c] :
        /\ requests[c] = {}
        /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]
        /\ schedule' = <<c>> \o (EXCEPT schedule WHERE [i \in 1..Len(schedule) |-> IF schedule[i] = c THEN FALSE ELSE TRUE])
        /\ requests' = requests
    \/ \E perm \in Permutations({c \in Clients | requests[c] /= {} \ /\ c \notin DOMAIN schedule}) :
        /\ schedule' = schedule \o <<perm>>
        /\ heldResources' = heldResources
        /\ requests' = requests

Spec ==
    /\ Init
    /\ [][Next]_<<heldResources, requests, schedule>>

SafetyProperties ==
    /\ \A r \in Resources : Cardinality({c \in Clients | r \in heldResources[c]}) <= 1
    /\ \A c \in DOMAIN schedule : requests[c] /= {}
    /\ \A s \in SUBSEQ(schedule) :
        \/ requests[s[1]] = {}
        \/ \E i \in 1..Len(s) : \A j \in 1..i-1 : heldResources[s[j]] \cap requests[s[i]] = {}

LivenessProperties ==
    /\ \A c \in Clients, r \in Requests[c] :
        <>[](r \in heldResources[c])
    /\ \A c \in Clients :
        <>[](\A r \in Requests[c] : r \notin heldResources[c]) => (heldResources[c] = {})
    /\ \A c \in Clients :
        <>(\A r \in Requests[c] : r \in heldResources[c])

Fairness ==
    WF_next(schedule)

THEOREM Spec => []SafetyProperties
THEOREM Spec => <>LivenessProperties

=============================================================================