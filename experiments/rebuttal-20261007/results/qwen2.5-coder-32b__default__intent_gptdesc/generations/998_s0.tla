------------------------------- MODULE ResourceAllocator -------------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS 
    Clients, Resources

VARIABLES 
    held, requested, schedule

Init == /\ held = [c \in Clients |-> {}]
        /\ requested = [c \in Clients |-> {}]
        /\ schedule = <<>>

Next ==
    \/ \E c \in Clients, r \subseteq Resources \ :
         /\ requested[c] = {}
         /\ r /= {}
         /\ UNCHANGED [held EXCEPT ![c] = r]
         /\ UNCHANGED requested
         /\ UNCHANGED schedule
    \/ \E c \in Clients, r \in Resources \ :
         /\ r \in requested[c]
         /\ r \notin held[c]
         /\ \A c' \in Head(schedule) : r \notin requested[c']
         /\ UNCHANGED [held EXCEPT ![c] = held[c] \cup {r}]
         /\ UNCHANGED [requested EXCEPT ![c] = requested[c] \ {r}]
         /\ UNCHANGED schedule
    \/ \E c \in Clients, r \in Resources \ :
         /\ r \in held[c]
         /\ UNCHANGED [held EXCEPT ![c] = held[c] \ {r}]
         /\ UNCHANGED requested
         /\ UNCHANGED schedule
    \/ \E s \in SUBSET Clients : 
         /\ requested[s] /= {}
         /\ schedule = Append(schedule, <<s>>)
         /\ UNCHANGED held
         /\ UNCHANGED requested

Spec == Init /\ [][Next]_<<held, requested, schedule>>

MutualExclusion ==
    \A r \in Resources, c1, c2 \in Clients :
        c1 # c2 => r \notin held[c1] \/ r \notin held[c2]

NoEarlyAllocation ==
    \A c \in Clients, r \in Resources :
        /\ r \in requested[c]
        /\ r \in held[c]
        => \A c' \in Head(schedule) : r \notin requested[c']

ScheduledRequests ==
    \A c \in Clients :
        /\ c \in DOMAIN schedule
        <=> requested[c] /= {}

AllocationFeasibility ==
    \A c \in Clients, s \in SUBSET Resources :
        /\ s \subseteq requested[c]
        => \E perm \in Permutations(DOMAIN schedule) :
            \A i \in 1..Len(perm), j \in 1..i-1 :
                requested[perm[i]] \cap held[perm[j]] = {}

ClientProgress ==
    \A c \in Clients, s \in SUBSET Resources :
        /\ s \subseteq requested[c]
        => <>(\E perm \in Permutations(DOMAIN schedule) :
            \A i \in 1..Len(perm), j \in 1..i-1 :
                requested[perm[i]] \cap held[perm[j]] = {}
            /\ \A r \in s : r \in held[c])

AllocatorProgress ==
    \A c \in Clients, s \in SUBSET Resources :
        /\ s \subseteq requested[c]
        => <>(\E perm \in Permutations(DOMAIN schedule) :
            \A i \in 1..Len(perm), j \in 1..i-1 :
                requested[perm[i]] \cap held[perm[j]] = {}
            /\ \A r \in s : r \notin held[c]
            => <>(\E r' \in s : r' \in held[c]))

ResourceAllocation ==
    \A c \in Clients, s \in SUBSET Resources :
        /\ s \subseteq requested[c]
        => <>[](\E perm \in Permutations(DOMAIN schedule) :
            \A i \in 1..Len(perm), j \in 1..i-1 :
                requested[perm[i]] \cap held[perm[j]] = {}
            /\ \A r \in s : r \in held[c])

ClientRequestSatisfaction ==
    \A c \in Clients, s \in SUBSET Resources :
        /\ s \subseteq requested[c]
        => <>[](\E perm \in Permutations(DOMAIN schedule) :
            \A i \in 1..Len(perm), j \in 1..i-1 :
                requested[perm[i]] \cap held[perm[j]] = {}
            /\ \A r \in s : r \in held[c])

Fairness ==
    WF_next(schedule)

THEOREM Spec => []MutualExclusion
THEOREM Spec => []NoEarlyAllocation
THEOREM Spec => []ScheduledRequests
THEOREM Spec => []AllocationFeasibility
THEOREM Spec => <>[]ClientProgress
THEOREM Spec => <>[]AllocatorProgress
THEOREM Spec => <>[]ResourceAllocation
THEOREM Spec => <>[]ClientRequestSatisfaction

=============================================================================