------------------------------- MODULE RollingDeployment -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Servers
VARIABLES lbServers, updatingServers, serverVersions, phase

Init == /\ lbServers = Servers
        /\ updatingServers = {}
        /\ serverVersions \in [Servers -> {0}]
        /\ phase = 1

Next ==
    \/ /\ phase = 1
       /\ \E s \in lbServers : ~ (s \in updatingServers)
       /\ /\ E' \in SUBSET lbServers \ {s} :
            /\ updatingServers' = updatingServers \cup {s}
            /\ serverVersions' = [serverVersions EXCEPT ![s] = 1]
            /\ lbServers' = E'
            /\ phase' = 2
    \/ /\ phase = 2
       /\ \A s \in lbServers : serverVersions[s] = 1
       /\ /\ E' \in SUBSET Servers :
            /\ updatingServers' = updatingServers \cup lbServers
            /\ serverVersions' = [serverVersions EXCEPT ![s \in lbServers] = 1]
            /\ lbServers' = E'
            /\ phase' = 3
    \/ /\ phase = 3
       /\ \A s \in updatingServers : serverVersions[s] = 1
       /\ updatingServers' = {}
       /\ lbServers' = Servers
       /\ phase' = 1

Spec ==
    /\ Init
    /\ [][Next]_<<lbServers, updatingServers, serverVersions, phase>>
    /\ <><Termination>_<<lbServers, updatingServers, serverVersions, phase>>

ZeroDowntime == \A s \in lbServers : ~ (serverVersions[s] = 1)

SameVersion ==
    LET currentVersion == CHOOSE v \in {serverVersions[s] : s \in lbServers} : TRUE
    IN  \A s \in lbServers : serverVersions[s] = currentVersion

Termination ==
    /\ \A s \in Servers : serverVersions[s] = 1
    /\ phase = 1

=============================================================================