------------------------------ MODULE ResourceAllocator ------------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Resources, Clients

VARIABLES held, requested

Init == 
    /\ held = [c \in Clients |-> {}]
    /\ requested = [c \in Clients |-> 0]

Next ==
    \/ \E c \in Clients : 
        \/ /\ requested[c] = 0
           /\ \E r \in Resources : ~ (r \in UNION {held[c] : c \in Clients})
           /\ requested' = [requested EXCEPT ![c] = requested[c] + 1]
              /\ held' = held
        \/ /\ requested[c] > 0
           /\ \E r \in requested[c] : r \notin held[c]
           /\ \E r \in Resources \ (UNION {held[c] : c \in Clients}) : 
                requested' = [requested EXCEPT ![c] = requested[c] - {r}]
                /\ held' = [held EXCEPT ![c] = held[c] \cup {r}]
        \/ /\ requested[c] > 0
           /\ r \in held[c]
           /\ requested' = [requested EXCEPT ![c] = requested[c]]
              /\ held' = [held EXCEPT ![c] = held[c] \ {r}]
    \/ /\ TRUE
       /\ requested' = requested
          /\ held' = held

TypeOK ==
    /\ \A c \in Clients : requested[c] \subseteq Resources
    /\ \A c \in Clients, r \in Resources : r \in held[c] => r \notin requested[c]

MutualExclusion ==
    \A r \in Resources : \A c1, c2 \in Clients : 
        \/ c1 = c2
        \/ ~(r \in held[c1] /\ r \in held[c2])

Safety == TypeOK /\ MutualExclusion

EventualReturn ==
    WF_next(\E c \in Clients, r \in Resources : requested[c] > 0 /\ r \notin held[c] /\ ~ (r \in UNION {held[c] : c \in Clients}))

EventualObtainment ==
    SF_next(\A c \in Clients : requested[c] = 0)

NoUnsatisfiedRequests ==
    WF_next(\A c \in Clients : requested[c] = 0)

Spec ==
    Spec_Theorem == 
        /\ Init
        /\ [][Next]_<<requested, held>>
        /\ Safety
        /\ EventualReturn
        /\ EventualObtainment
        /\ NoUnsatisfiedRequests

Symmetry ==
    \A perm \in Permutations(Resources) :
        <\A c \in Clients : perm[held[c]]>,
         \A c \in Clients : perm[requested[c]]> \in Spec_Theorem

CounterexampleValueStructure ==
    [Clients |-> {"C1", "C2"},
     Resources |-> {"R1", "R2"},
     held |-> ["C1" |-> {}, "C2" |-> {}],
     requested |-> ["C1" |-> {}, "C2" |-> {"R1"}]]

=============================================================================