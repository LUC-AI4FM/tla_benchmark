                    /\ (<<c, r-1>> = LV(r-1) => MayVote(r-1)))
                    => <<c, r-1>> \in P
            /\ LeaderRule(n, r, P)
            /\ vs' = vs \cup {<<n, r>>}
            /\ es' = es \cup ({<<n, r>>} \X P)
            /\ round' = [round EXCEPT ![n] = r]
            /\ log' = [log EXCEPT ![n] = CommitLog(log[n], r, P)]

\* A Byzantine node creates a vertex. It cannot equivocate (one vertex per
\* round) and must reference a quorum of previous-round vertices. Leader
\* vertices must satisfy the leader rule (enforced by validity checks).
ByzStep ==
    /\ \E b \in F, r \in R :
         /\ <<b, r>> \notin vs
         /\ \/ /\ r = 1
               /\ vs' = vs \cup {<<b, 1>>}
               /\ UNCHANGED es
            \/ /\ r > 1
               /\ \E P \in SUBSET VsAt(r - 1) :
                    /\ IsQuorum(Nodes(P))
                    /\ LeaderRule(b, r, P)
                    /\ vs' = vs \cup {<<b, r>>}
                    /\ es' = es \cup ({<<b, r>>} \X P)
    /\ UNCHANGED <<round, log>>

\* All correct nodes have reached the last round: allow stuttering
Terminated ==
    /\ \A n \in Correct : round[n] = MaxRound
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Correct : Start(n) \/ Advance(n)
    \/ ByzStep
    \/ Terminated

Fairness == \A n \in Correct : WF_vars(Start(n) \/ Advance(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

Agreement ==
    \A n, m \in Correct : IsPrefix(log[n], log[m]) \/ IsPrefix(log[m], log[n])

\* After GST, the vertices of correct leaders eventually appear in all logs
\* of correct nodes (for rounds that can still be committed).
Liveness ==
    Fairness =>
      \A r \in R :
        (/\ r >= GST
         /\ r + 2 <= MaxRound
         /\ Leader(r) \in Correct)
          => <>(\A n \in Correct : LV(r) \in Range(log[n]))

=============================================================================
```