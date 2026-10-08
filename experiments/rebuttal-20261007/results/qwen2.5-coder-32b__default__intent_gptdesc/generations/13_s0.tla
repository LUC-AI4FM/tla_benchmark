------------------------------- MODULE RollingUpdate -------------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    Servers,  \* The set of servers
    Updating  \* Distinguished representation for the "updating" state

VARIABLES 
    version,  \* Maps each server to its current version or Updating
    loadBalancedSet  \* Set of servers currently receiving traffic

Init == /\ version \in [Servers -> {Updating} \cup {"old", "new"}]
        /\ loadBalancedSet = Servers

Next ==
    \/ \/ \E s \in loadBalancedSet : 
            /\ version[s] = "old"
            /\ version' = [version EXCEPT ![s] = Updating]
            /\ loadBalancedSet' = loadBalancedSet \ {s}
       \/ \E s \notin loadBalancedSet :
            /\ version[s] = Updating
            /\ version' = [version EXCEPT ![s] = "new"]
            /\ loadBalancedSet' = loadBalancedSet \cup {s}
       \/ \/ \E S \subseteq loadBalancedSet, S /= {} :
                /\ version' = [s \in Servers |-> IF s \notin S THEN version[s]
                                                   ELSE IF version[s] = "old" THEN Updating
                                                   ELSE version[s]]
                /\ loadBalancedSet' = loadBalancedSet \ S
           \/ \E S \subseteq Servers, S \subseteq {s \in Servers | version[s] = Updating} :
                /\ version' = [s \in Servers |-> IF s \notin S THEN version[s]
                                                   ELSE "new"]
                /\ loadBalancedSet' = loadBalancedSet \cup S

Spec ==
    /\ Init
    /\ [][Next]_<<version, loadBalancedSet>>
    /\ WF_next(<<version, loadBalancedSet>>)

VersionHomogeneous ==
    \/ loadBalancedSet = {}
    \/ (\A s1, s2 \in loadBalancedSet : version[s1] = version[s2])

ZeroDowntime ==
    /\ loadBalancedSet /= {}

Termination ==
    /\ \A s \in Servers : version[s] = "new"

SpecWithProperties ==
    Spec
    /\ []VersionHomogeneous
    /\ []ZeroDowntime
    /\ <>(Termination)

=============================================================================