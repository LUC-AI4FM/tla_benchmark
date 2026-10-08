------------------------------ MODULE AtomicCommitment ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Procs,                            \* Set of processes
    MaxF                              \* Maximum number of faulty processes

VARIABLES 
    vote,                             \* Vote (YES or NO) for each process
    suspected,                        \* Suspected set by failure detector
    outbox,                           \* Outgoing messages queue for each process
    inbox,                            \* Incoming messages queue for each process
    decision                          \* Decision made by the algorithm: NONE, COMMIT, ABORT

Init == 
    /\ vote \in [Procs -> {"YES", "NO"}]
    /\ suspected = {}
    /\ outbox \in [Procs -> Seq({})]
    /\ inbox \in [Procs -> Seq({})]
    /\ decision = "NONE"
    /\ \/ (\A p \in Procs: vote[p] = "YES")
       \/ (\A p \in Procs: vote[p] = "NO")

SendMsg ==
    CHOOSE <<p, m>> \in UNION {outbox[p]: p \in Procs}:
        LET r == CHOOSE q \in (Procs \ {p}) \ suspected: TRUE
        IN /\ outbox' = [outbox EXCEPT ![p] = Tail(outbox[p])]
           /\ inbox' = [inbox EXCEPT ![r] = Append(inbox[r], m)]

ProcessAction ==
    LET p == CHOOSE q \in Procs \ suspected: TRUE
    IN \/ /\ vote[p] = "YES"
          /\ decision = "NONE"
          /\ \E m \in {"COMMIT", "ABORT"}:
             outbox' = [outbox EXCEPT ![p] = Append(outbox[p], <<p, m>>)]
       \/ /\ vote[p] = "NO"
          /\ decision = "NONE"
          /\ \E m \in {"ABORT"}:
             outbox' = [outbox EXCEPT ![p] = Append(outbox[p], <<p, m>>)]

HandleMsg ==
    LET p == CHOOSE q \in Procs \ suspected: TRUE
        m == Head(inbox[p])
    IN /\ inbox' = [inbox EXCEPT ![p] = Tail(inbox[p])]
       /\ \/ decision = "NONE"
          /\ m[2] = "COMMIT"
          /\ decision' = "COMMIT"
       \/ decision = "NONE"
          /\ m[2] = "ABORT"
          /\ decision' = "ABORT"

Next ==
    \/ SendMsg
    \/ ProcessAction
    \/ HandleMsg

Spec ==
    Init /\ [][Next]_<<vote, suspected, outbox, inbox, decision>> 
        /\ WF_[<>]_SendMsg
        /\ SF_[<>]_ProcessAction

TypeInvariant ==
    /\ vote \in [Procs -> {"YES", "NO"}]
    /\ suspected \subseteq Procs
    /\ outbox \in [Procs -> Seq({})]
    /\ inbox \in [Procs -> Seq({})]
    /\ decision \in {"NONE", "COMMIT", "ABORT"}

Agreement ==
    /\ decision = "COMMIT" => (\A p \in Procs: vote[p] = "YES")
    /\ decision = "ABORT" => (\E p \in Procs: vote[p] = "NO")

AbortValidity ==
    decision = "ABORT" => |suspected| > MaxF

CommitValidity ==
    decision = "COMMIT" => |suspected| <= MaxF

Termination ==
    \/ decision = "COMMIT"
    \/ decision = "ABORT"

EventualCommit ==
    <>(decision = "COMMIT")

Properties ==
    /\ TypeInvariant
    /\ Agreement
    /\ AbortValidity
    /\ CommitValidity
    /\ Termination
    /\ EventualCommit

=============================================================================