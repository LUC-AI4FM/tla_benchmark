------------------------------- MODULE ResourceAllocator -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Clients, Resources
ASSUME /\ Clients \subseteq Nat
       /\ Resources \subseteq Nat
       /\ Cardinality(Resources) > 0

VARIABLES held, requested

Init == /\ held = [c \in Clients |-> {}]
        /\ requested = [c \in Clients |-> {}]

Next ==
    \/ \E c \in Clients, r \in SUBSET Resources :
         /\ r /= {}
         /\ requested[c] = {}
         /\ held[c] = {}
         /\ requested' = [requested EXCEPT ![c] = r]
         /\ UNCHANGED held
    \/ \E c \in Clients, g \in SUBSET Resources :
         /\ g /= {}
         /\ g \subseteq requested[c]
         /\ g \subseteq (Resources \ {r \in Resources : \E d \in Clients : r \in held[d]})
         /\ requested' = [requested EXCEPT ![c] = requested[c] \ g]
         /\ held' = [held EXCEPT ![c] = held[c] \cup g]
    \/ \E c \in Clients, h \in SUBSET Resources :
         /\ h /= {}
         /\ h \subseteq held[c]
         /\ held' = [held EXCEPT ![c] = held[c] \ h]
         /\ UNCHANGED requested

Spec ==
    /\ Init
    /\ [][Next]_<<Clients>>
    /\ WF_next(<<Clients>>)

Exclusivity == \A r \in Resources : Cardinality({c \in Clients : r \in held[c]}) <= 1

WellFormedState == 
    /\ \A c \in Clients : requested[c] \subseteq Resources
    /\ \A c \in Clients : held[c] \subseteq Resources

Liveness ==
    /\ \A c \in Clients, r \in Resources :
         \/ <<c, {r}>> \notin (Init \cup [][Next]_<<Clients>>) 
         \/ <>(requested[c] = {} /\ r \in held[c])
    /\ \A c \in Clients : <>[](requested[c] = {})
    /\ \A c \in Clients : WF_next(<<c>>)

THEOREM Spec => []Exclusivity
THEOREM Spec => [](WellFormedState)
THEOREM Spec => Liveness

=============================================================================