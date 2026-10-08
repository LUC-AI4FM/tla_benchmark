------------------------------- MODULE ResourceAllocator -------------------------------
EXTENDS TLC, Integers, FiniteSets

CONSTANTS Resources, Clients
ASSUME Resources \subseteq Nat /\ Cardinality(Resources) > 0
ASSUME Clients \subseteq Nat /\ Cardinality(Clients) > 0

VARIABLES heldResources, requestedResources, unsatisfiedRequests

Init == 
  /\ heldResources = [c \in Clients |-> {}]
  /\ requestedResources = [c \in Clients |-> {}]
  /\ unsatisfiedRequests = {}

Next ==
  \/ \/ c \in Clients
     \/ ~ (\E r \in Resources : r \in heldResources[c])
     \/ ~ (requestedResources[c] /= {})
     \/ \/ newRequest \subseteq Resources
        \/ requestedResources' = [requestedResources EXCEPT ![c] = newRequest]
        \/ unsatisfiedRequests' = unsatisfiedRequests \cup {c}
  \/ \/ c \in Clients
     \/ r \in heldResources[c]
     \/ \/ /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]
        \/ /\ IF r \notin requestedResources[c] THEN requestedResources' = requestedResources
           ELSE requestedResources' = [requestedResources EXCEPT ![c] = requestedResources[c] \ {r}]
        \/ /\ IF (requestedResources'[c] = {}) /\ (c \in unsatisfiedRequests) 
              THEN unsatisfiedRequests' = unsatisfiedRequests \ {c}
              ELSE unsatisfiedRequests' = unsatisfiedRequests
  \/ \/ c \in Clients
     \/ r \notin heldResources[c]
     \/ r \in requestedResources[c]
     \/ ~ (\E rc \in Clients : rc /= c /\ r \in heldResources[rc])
     \/ \/ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup {r}]
        \/ requestedResources' = requestedResources
        \/ unsatisfiedRequests' = IF (requestedResources'[c] = {}) /\ (c \in unsatisfiedRequests) 
                                  THEN unsatisfiedRequests \ {c}
                                  ELSE unsatisfiedRequests

Spec ==
  INIT Init
  /\ SF_<<Next>>

TypeOk ==
  /\ (\A c \in Clients : heldResources[c] \subseteq Resources)
  /\ (\A c \in Clients : requestedResources[c] \subseteq Resources)
  /\ unsatisfiedRequests \subseteq Clients

MutualExclusion ==
  \A r \in Resources, c1, c2 \in Clients : (c1 /= c2) => ~(r \in heldResources[c1] /\ r \in heldResources[c2])

EventualReturn ==
  WF_<<Next>> (\E c \in Clients : heldResources[c] = {})

EventualObtainment ==
  WF_<<Next>> (\A c \in Clients : unsatisfiedRequests'[c] = {})

NoUnsatisfiedForever ==
  SF_<<Next>> (unsatisfiedRequests = {})

Spec1 == Spec /\ TypeOk /\ MutualExclusion /\ EventualReturn /\ EventualObtainment /\ NoUnsatisfiedForever

Symmetry ==
  LET permute \in [Clients -> Clients] : 
      \/ /\ PERMUTATIONS(Clients, permute)
      \/ /\ (\A c \in Clients : heldResources[permute[c]] = {r \in Resources : r \in heldResources[c]})
      \/ /\ (\A c \in Clients : requestedResources[permute[c]] = {r \in Resources : r \in requestedResources[c]})
      \/ /\ (unsatisfiedRequests = {permute[c] : c \in unsatisfiedRequests})
  IN 
    Spec1 /\ [][Symmetry]_<<Next>>

CONSTANT ConcreteValues
ASSUME TypeOk /\ MutualExclusion /\ EventualReturn /\ EventualObtainment /\ NoUnsatisfiedForever

=============================================================================