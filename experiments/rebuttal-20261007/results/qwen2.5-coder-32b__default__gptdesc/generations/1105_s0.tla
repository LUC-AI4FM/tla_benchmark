------------------------------- MODULE AsyncCommit --------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Procs \* The set of processes
    F     \* The maximum number of faulty processes

VARIABLES 
    vote,   \* vote[p] is the initial vote of process p (either "YES" or "NO")
    state,  \* state[p] is the current state of process p ("INIT", "ABORT", "COMMIT", "WAITING")
    msg,    \* msg[p][q] is the message sent from process q to process p
    suspect \* suspect[p] is the set of processes suspected by process p

Init == 
    /\ vote \in [Procs -> {"YES", "NO"}]
    /\ \/ (\A p \in Procs: vote[p] = "YES")
       \/ (\A p \in Procs: vote[p] = "NO")
    /\ state \in [Procs -> {"INIT"}]
    /\ msg \in [Procs -> [Procs -> BOOLEAN]]
    /\ suspect \in [Procs -> {}]

Next == 
    \/ \E p \in Procs, q \in (Procs \ {p}): 
        \/ /\ state[p] = "WAITING"
           /\ ~ (q \in suspect[p])
           /\ msg[p][q]
           /\ UNCHANGED <<vote, state EXCEPT [p <- IF vote[q] = "NO" THEN "ABORT" ELSE state[p]], msg, suspect>>
        \/ /\ state[p] = "INIT"
           /\ UNCHANGED <<vote, state EXCEPT [p <- "WAITING"], msg, suspect>>
    \/ \E p \in Procs:
        \/ /\ state[p] = "WAITING"
           /\ (\A q \in (Procs \ {p}): q \in suspect[p])
           /\ UNCHANGED <<vote, state EXCEPT [p <- "ABORT"], msg, suspect>>
        \/ /\ state[p] = "INIT"
           /\ UNCHANGED <<vote, state EXCEPT [p <- "WAITING"], msg, suspect>>
    \/ \E p \in Procs, q \in (Procs \ {p}):
        \/ /\ state[q] = "ABORT"
           /\ ~ (q \in suspect[p])
           /\ UNCHANGED <<vote, state EXCEPT [p <- "ABORT"], msg EXCEPT [[p][q] <- TRUE], suspect>>
        \/ /\ state[q] = "COMMIT"
           /\ ~ (q \in suspect[p])
           /\ UNCHANGED <<vote, state EXCEPT [p <- "COMMIT"], msg EXCEPT [[p][q] <- TRUE], suspect>>
    \/ \E p \in Procs:
        \/ /\ state[p] = "WAITING"
           /\ (\A q \in (Procs \ {p}): state[q] = "YES" \/ q \in suspect[p])
           /\ UNCHANGED <<vote, state EXCEPT [p <- "COMMIT"], msg, suspect>>
        \/ /\ state[p] = "WAITING"
           /\ (\E q \in (Procs \ {p}): state[q] = "NO" /\ ~ (q \in suspect[p]))
           /\ UNCHANGED <<vote, state EXCEPT [p <- "ABORT"], msg, suspect>>

Spec == 
    Init /\ [][Next]_<<vote, state, msg, suspect>> /\ WFNext

WFNext == 
    WFFair({s \in (Procs -> {"INIT", "WAITING", "ABORT", "COMMIT"}) : s = state} \ {state})

TypeInvariant ==
    /\ vote \in [Procs -> {"YES", "NO"}]
    /\ state \in [Procs -> {"INIT", "WAITING", "ABORT", "COMMIT"}]
    /\ msg \in [Procs -> [Procs -> BOOLEAN]]
    /\ suspect \in [Procs -> SUBSET Procs]

Agreement ==
    \/ (\A p, q \in Procs: state[p] = "ABORT" \/ state[q] = "ABORT")
    \/ (\E v \in {"YES", "NO"}: \A p \in Procs: state[p] = "COMMIT" => vote[p] = v)

AbortValidity ==
    /\ (\A p \in Procs: state[p] = "ABORT" => (\E q \in (Procs \ {p}): state[q] = "NO" /\ ~ (q \in suspect[p])))
    \/ (\A p \in Procs: state[p] = "ABORT" => (\A q \in (Procs \ {p}): q \in suspect[p]))

CommitValidity ==
    /\ (\A p \in Procs: state[p] = "COMMIT" => (\A q \in (Procs \ {p}): vote[q] = vote[p]))
    \/ (\A p \in Procs: state[p] = "COMMIT" => (\A q \in (Procs \ {p}): q \in suspect[p]))

Termination ==
    []<>(\E p \in Procs: state[p] \in {"ABORT", "COMMIT"})

EventualCommit ==
    <>(\A p \in Procs: state[p] = "COMMIT")

THEOREM Spec => []TypeInvariant
THEOREM Spec => []Agreement
THEOREM Spec => []AbortValidity
THEOREM Spec => []CommitValidity
THEOREM Spec => []Termination
THEOREM Spec => <>EventualCommit

=============================================================================