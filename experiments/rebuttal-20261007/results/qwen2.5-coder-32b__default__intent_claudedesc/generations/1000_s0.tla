------------------------------- MODULE ResourceAllocator -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources
ASSUME /\ Clients \subseteq Nat
       /\ Resources \subseteq Nat
       /\ Cardinality(Clients) > 0
       /\ Cardinality(Resources) > 0

VARIABLES held, requested, available

Init == /\ held = [c \in Clients |-> {}]
        /\ requested = [c \in Clients |-> {}]
        /\ available = Resources

Next ==
    \/ \E c \in Clients, r \subseteq Resources \: 
         (requested[c] = {} /\ held[c] = {}) 
      -> requested' = [requested EXCEPT ![c] = r]
         /\ UNCHANGED <<held, available>>
    \/ \E c \in Clients, r \subseteq requested[c], a \subseteq available, a /= {} : 
         -> held' = [held EXCEPT ![c] = held[c] \cup a]
            /\ available' = available \ {a}
            /\ UNCHANGED requested
    \/ \E c \in Clients, r \subseteq held[c] :
         (requested[c] = {} \/ requested[c] \subseteq held[c])
      -> held' = [held EXCEPT ![c] = held[c] \ r]
         /\ available' = available \cup r
         /\ UNCHANGED requested

Spec ==
    /\ Init
    /\ [][Next]_<<held, requested, available>>
    /\ WF_Strong(Next, {c \in Clients | requested[c] /= {}})
    /\ SF_Weak(Next, {c \in Clients | requested[c] = {} /\ held[c] /= {}})

MutualExclusion ==
    \A r \in Resources : Cardinality({c \in Clients | r \in held[c]}) <= 1

EventualReturn ==
    \A c \in Clients :
        [](requested[c] = {} => <>[] (held[c] = {}))

EventualAllocation ==
    \A c \in Clients, r \in requested[c] :
        <>(r \in held[c])

InfiniteSatisfiability ==
    \A c \in Clients :
        []<>(\E r \subseteq requested[c] : r \subseteq held[c]) => <>[](\A r \in requested[c] : r \in held[c])

THEOREM Spec => []MutualExclusion
THEOREM Spec => EventualReturn
THEOREM Spec => EventualAllocation
THEOREM Spec => InfiniteSatisfiability

=============================================================================