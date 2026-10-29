```tla
HANGED vars

(***************************************************************************)
(* Next-state relation and full specification.                             *)
(***************************************************************************)
Next ==
    \/ \E c \in pending, k \in Kinds : ClientRequest(c, k)
    \/ \E r \in Replicas, b \in Ballots : BecomeLeader(r, b)
    \/ \E r \in Replicas, m \in msgs : HandlePrepare(r, m)
    \/ \E r \in Replicas : BecomePrepared(r)
    \/ \E r \in Replicas, c \in CmdRecs : Propose(r, c)
    \/ \E r \in Replicas, m \in msgs : HandleAccept(r, m)
    \/ \E r \in Replicas, s \in Slots : Commit(r, s)
    \/ \E r \in Replicas : Execute(r)
    \/ Terminate

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety: every Ack follows its Req, each command is acked at most once,  *)
(* and each acked value is consistent with a write that was requested.     *)
(***************************************************************************)
AckAfterReq ==
    \A j \in 1..Len(observed) :
        observed[j].type = "Ack" =>
            \E i \in 1..(j-1) : /\ observed[i].type = "Req"
                                /\ observed[i].cmd = observed[j].cmd

AckOnce ==
    \A i, j \in 1..Len(observed) :
        /\ observed[i].type = "Ack"
        /\ observed[j].type = "Ack"
        /\ observed[i].cmd.id = observed[j].cmd.id
        => i = j

ReadValid ==
    \A j \in 1..Len(observed) :
        /\ observed[j].type = "Ack"
        /\ observed[j].cmd.kind = "Read"
        /\ observed[j].val /= 0
        => \E i \in 1..(j-1) : /\ observed[i].type = "Req"
                               /\ observed[i].cmd.kind = "Write"
                               /\ observed[i].cmd.id = observed[j].val

Linearizability == AckAfterReq /\ AckOnce /\ ReadValid

=============================================================================
```