------------------------------- MODULE ResourceAllocator -------------------------------

CONSTANTS 
    Clients,                \* Finite set of clients
    Resources               \* Finite set of resources

VARIABLES 
    heldResources,          \* Function from clients to sets of resources they hold
    requestedResources,     \* Function from clients to sets of resources they request
    schedule                \* Sequence of clients representing the order in which requests are considered

ASSUME 
    FINITE Clients /\ FINITE Resources

CONSTANTS Init

Init == 
    /\ heldResources = [c \in Clients |-> {}]
    /\ requestedResources = [c \in Clients |-> {}]
    /\ schedule = <<>>

VARIABLES pc

Next ==
    \/ \E c \in Clients : 
        /\ requestedResources[c] = {}
        /\ heldResources[c] = {}
        /\ UNCHANGED <<heldResources EXCEPT [c \-> {}], requestedResources, schedule>>
    \/ \E c \in Clients :
        /\ requestedResources[c] /= {}
        /\ heldResources[c] = {}
        /\ \E r \in Resources \ (DOMAIN heldResources) : 
            /\ r \notin UNION {heldResources[c'] : c' \in Clients}
            /\ UNCHANGED <<requestedResources, schedule>>
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup {r}]
    \/ \E c \in Clients :
        /\ requestedResources[c] /= {}
        /\ heldResources[c] /= {}
        /\ \E r \in Resources \ (DOMAIN heldResources) : 
            /\ r \notin UNION {heldResources[c'] : c' \in Clients}
            /\ r \notin heldResources[c]
            /\ UNCHANGED <<requestedResources, schedule>>
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup {r}]
    \/ \E c \in Clients :
        /\ requestedResources[c] /= {}
        /\ heldResources[c] /= {}
        /\ \E r \in heldResources[c] : 
            /\ UNCHANGED <<requestedResources, schedule>>
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]
    \/ \E c \in Clients :
        /\ requestedResources[c] = {}
        /\ heldResources[c] /= {}
        /\ \E r \in heldResources[c] : 
            /\ UNCHANGED <<requestedResources, schedule>>
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]
    \/ \E c \in Clients :
        /\ requestedResources[c] = {}
        /\ heldResources[c] = {}
        /\ \E r \in Resources : 
            /\ r \notin UNION {heldResources[c'] : c' \in Clients}
            /\ UNCHANGED <<schedule>>
            /\ requestedResources' = [requestedResources EXCEPT ![c] = requestedResources[c] \cup {r}]
    \/ schedule # <<>> /\ \E i \in 1..Len(schedule) :
        LET c == schedule[i]
        IN
        /\ requestedResources[c] /= {}
        /\ heldResources[c] = {}
        /\ \E r \in Resources \ (DOMAIN heldResources) : 
            /\ r \notin UNION {heldResources[c'] : c' \in Clients}
            /\ UNCHANGED <<requestedResources>>
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup {r}]
            /\ schedule' = Append(<<>>, Tail(schedule))
    \/ schedule # <<>> /\ \E i \in 1..Len(schedule) :
        LET c == schedule[i]
        IN
        /\ requestedResources[c] /= {}
        /\ heldResources[c] /= {}
        /\ \E r \in Resources \ (DOMAIN heldResources) : 
            /\ r \notin UNION {heldResources[c'] : c' \in Clients}
            /\ r \notin heldResources[c]
            /\ UNCHANGED <<requestedResources>>
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup {r}]
            /\ schedule' = Append(<<>>, Tail(schedule))
    \/ schedule # <<>> /\ \E i \in 1..Len(schedule) :
        LET c == schedule[i]
        IN
        /\ requestedResources[c] /= {}
        /\ heldResources[c] /= {}
        /\ \E r \in heldResources[c] : 
            /\ UNCHANGED <<requestedResources>>
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]
            /\ schedule' = Append(<<>>, Tail(schedule))
    \/ schedule # <<>> /\ \E i \in 1..Len(schedule) :
        LET c == schedule[i]
        IN
        /\ requestedResources[c] = {}
        /\ heldResources[c] /= {}
        /\ \E r \in heldResources[c] : 
            /\ UNCHANGED <<requestedResources>>
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]
            /\ schedule' = Append(<<>>, Tail(schedule))
    \/ schedule # <<>> /\ \E i \in 1..Len(schedule) :
        LET c == schedule[i]
        IN
        /\ requestedResources[c] = {}
        /\ heldResources[c] = {}
        /\ \E r \in Resources : 
            /\ r \notin UNION {heldResources[c'] : c' \in Clients}
            /\ UNCHANGED <<requestedResources>>
            /\ requestedResources' = [requestedResources EXCEPT ![c] = requestedResources[c] \cup {r}]
            /\ schedule' = Append(<<>>, Tail(schedule))
    \/ schedule # <<>> /\ \E i \in 1..Len(schedule) :
        LET c == schedule[i]
        IN
        /\ requestedResources[c] /= {}
        /\ heldResources[c] = {}
        /\ \A r \in Resources : 
            (r \in UNION {heldResources[c'] : c' \in Clients} \/ r \in heldResources[c])
            /\ UNCHANGED <<requestedResources, heldResources>>
            /\ schedule' = Append(<<>>, Tail(schedule))
    \/ schedule # <<>> /\ \E i \in 1..Len(schedule) :
        LET c == schedule[i]
        IN
        /\ requestedResources[c] /= {}
        /\ heldResources[c] /= {}
        /\ \A r \in Resources : 
            (r \in UNION {heldResources[c'] : c' \in Clients} \/ r \in heldResources[c])
            /\ UNCHANGED <<requestedResources, heldResources>>
            /\ schedule' = Append(<<>>, Tail(schedule))
    \/ schedule # <<>> /\ \E i \in 1..Len(schedule) :
        LET c == schedule[i]
        IN
        /\ requestedResources[c] = {}
        /\ heldResources[c] /= {}
        /\ \A r \in Resources : 
            (r \in UNION {heldResources[c'] : c' \in Clients} \/ r \in heldResources[c])
            /\ UNCHANGED <<requestedResources, heldResources>>
            /\ schedule' = Append(<<>>, Tail(schedule))
    \/ schedule # <<>> /\ \E i \in 1..Len(schedule) :
        LET c == schedule[i]
        IN
        /\ requestedResources[c] = {}
        /\ heldResources[c] = {}
        /\ \A r \in Resources : 
            (r \in UNION {heldResources[c'] : c' \in Clients} \/ r \in heldResources[c])
            /\ UNCHANGED <<requestedResources, heldResources>>
            /\ schedule' = Append(<<>>, Tail(schedule))
    \/ \E c \in Clients :
        /\ requestedResources[c] /= {}
        /\ heldResources[c] = {}
        /\ \A r \in Resources : 
            (r \in UNION {heldResources[c'] : c' \in Clients} \/ r \in heldResources[c])
            /\ UNCHANGED <<requestedResources, heldResources>>
            /\ schedule' = Append(schedule, <<c>>)
    \/ \E c \in Clients :
        /\ requestedResources[c] /= {}
        /\ heldResources[c] /= {}
        /\ \A r \in Resources : 
            (r \in UNION {heldResources[c'] : c' \in Clients} \/ r \in heldResources[c])
            /\ UNCHANGED <<requestedResources, heldResources>>
            /\ schedule' = Append(schedule, <<c>>)
    \/ \E c \in Clients :
        /\ requestedResources[c] = {}
        /\ heldResources[c] /= {}
        /\ \A r \in Resources : 
            (r \in UNION {heldResources[c'] : c' \in Clients} \/ r \in heldResources[c])
            /\ UNCHANGED <<requestedResources, heldResources>>
            /\ schedule' = Append(schedule, <<c>>)
    \/ \E c \in Clients :
        /\ requestedResources[c] = {}
        /\ heldResources[c] = {}
        /\ \A r \in Resources : 
            (r \in UNION {heldResources[c'] : c' \in Clients} \/ r \in heldResources[c])
            /\ UNCHANGED <<requestedResources, heldResources>>
            /\ schedule' = Append(schedule, <<c>>)

Spec == Init /\ [][Next]_<<heldResources, requestedResources, schedule>>

WF_heldResources ==
    WF_vars(heldResources) 

WF_requestedResources ==
    WF_vars(requestedResources)

WF_schedule ==
    WF_vars(schedule)

MutualExclusion ==
    \A c1, c2 \in Clients, r \in Resources :
        c1 # c2 => r \notin heldResources[c1] \/ r \notin heldResources[c2]

AllocatorInvariant ==
    /\ \A c \in Clients : requestedResources[c] = {} \/ heldResources[c] = {}
    /\ \A r \in Resources : 
        (Len({c \in Clients : r \in heldResources[c]}) <= 1)

EventuallyReturn ==
    \A c \in Clients :
        <>[] (\E r \in heldResources[c] : UNCHANGED <<requestedResources, schedule>> /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}])

EventuallyObtain ==
    \A c \in Clients :
        <>[] (requestedResources[c] /= {} => \E r \in requestedResources[c] : UNCHANGED <<requestedResources, schedule>> /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup {r}])

InfinitelyOftenSatisfied ==
    \A c \in Clients :
        <>[] (requestedResources[c] = {} /\ heldResources[c] /= {})

Fairness ==
    WF_heldResources
    /\ WF_requestedResources
    /\ WF_schedule

THEOREM Spec => []AllocatorInvariant

THEOREM Spec => MutualExclusion

THEOREM Spec => Fairness

THEOREM Spec => EventuallyReturn

THEOREM Spec => EventuallyObtain

THEOREM Spec => InfinitelyOftenSatisfied

=============================================================================