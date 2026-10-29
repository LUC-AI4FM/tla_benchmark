ually happens; message loss is never forced *)
Fairness ==
    /\ \A c \in Commands : WF_vars(Submit(c)) /\ WF_vars(Ack(c))
    /\ \A r \in Replicas :
          /\ WF_vars(\E b \in Ballots : Prepare(r, b))
          /\ WF_vars(\E m \in msgs : PrepareReply(r, m))
          /\ WF_vars(\E m \in msgs : AcceptReply(r, m))
          /\ WF_vars(\E m \in msgs : LearnCommit(r, m))
          /\ WF_vars(\E Q \in Quorums : BecomeLeader(r, Q))
          /\ WF_vars(\E s \in Slots, c \in Commands : Propose(r, s, c))
          /\ WF_vars(\E s \in Slots : FillHole(r, s))
          /\ WF_vars(\E s \in Slots : SendAccept(r, s))
          /\ WF_vars(\E s \in Slots, Q \in Quorums : Commit(r, s, Q))
          /\ WF_vars(Execute(r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Definitions used by the invariants *)

ChosenAt(s, c, b) ==
    \E Q \in Quorums : \A a \in Q :
        [type |-> "acceptReply", bal |-> b, src |-> a, dst |-> Owner(b),
         slot |-> s, cmd |-> c] \in sentMsgs

Chosen(s, c) == \E b \in Ballots : ChosenAt(s, c, b)

\* First slot at which c appears in r's applied log prefix
FirstSlot(r, c) ==
    CHOOSE s \in 1..applied[r] :
        /\ committed[r][s] = c
        /\ \A t \in 1..(s - 1) : committed[r][t] # c

\* Value of the key just before slot s is applied at r: the last effective write
ValueBefore(r, s) ==
    LET W == {t \in 1..(s - 1) : /\ committed[r][t] \in WriteCmds
                                 /\ FirstSlot(r, committed[r][t]) = t}
    IN  IF W = {} THEN InitVal
        ELSE committed[r][CHOOSE t \in W : \A u \in W : u <= t].val

-----------------------------------------------------------------------------
(* Safety invariants *)

QuorumIntersection == \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

\* No two different commands are ever chosen at the same slot
ChosenConsistency ==
    \A s \in Slots : \A c1, c2 \in LogCmds :
        Chosen(s, c1) /\ Chosen(s, c2) => c1 = c2

\* Every committed command was chosen by a quorum
CommittedIsChosen ==
    \A r \in Replicas, s \in Slots :
        committed[r][s] # None => Chosen(s, committed[r][s])

\* Committed logs never diverge between replicas
CommitAgreement ==
    \A r1, r2 \in Replicas, s \in Slots :
        (committed[r1][s] # None /\ committed[r2][s] # None)
            => committed[r1][s] = committed[r2][s]

\* A replica votes only at ballots it has promised
VotesBelowBallot ==
    \A r \in Replicas, s \in Slots : votes[r][s].bal <= curBallot[r]

\* Accept messages at higher ballots keep any value chosen at a lower ballot
AcceptPreservesChosen ==
    \A m \in sentMsgs :
        m.type = "accept" =>
            \A b \in Ballots, c \in LogCmds :
                (b < m.bal /\ ChosenAt(m.slot, c, b)) => m.cmd = c

\* A prepared leader's proposals keep every value chosen at a lower ballot
LeaderPreservesVotes ==
    \A r \in Replicas, s \in Slots, c \in LogCmds :
        (isLeader[r] /\ \E b \in Ballots : b < curBallot[r] /\ ChosenAt(s, c, b))
            => proposals[r][s] = c

\* Replicas agree on every command result
ResultsAgree ==
    \A r1, r2 \in Replicas, c \in Commands :
        (results[r1][c] # NoResult /\ results[r2][c] # NoResult)
            => results[r1][c] = results[r2][c]

\* A read returns the value of the last write serialized before it
ReadsConsistent ==
    \A r \in Replicas, c \in ReadCmds :
        results[r][c] # NoResult => results[r][c] = ValueBefore(r, FirstSlot(r, c))

-----------------------------------------------------------------------------
(* Linearizability.  The witness order is the first-slot order in the     *)
(* committed log.                                                          *)

\* Every acknowledgement follows its request and reports the serialized result
AckMatches ==
    \A i \in 1..Len(history) :
        history[i].kind = "ack" =>
            /\ \E j \in 1..(i - 1) :
                   history[j].kind = "req" /\ history[j].cmd = history[i].cmd
            /\ \A r \in Replicas :
                   results[r][history[i].cmd] # NoResult
                       => results[r][history[i].cmd] = history[i].res

\* If c1 was acknowledged before c2 was requested, c1 is serialized first
RealTimeOrder ==
    \A i, j \in 1..Len(history) :
        (i < j /\ history[i].kind = "ack" /\ history[j].kind = "req")
            => \A r \in Replicas :
                   history[j].cmd \in executed[r]
                       => /\ history[i].cmd \in executed[r]
                          /\ FirstSlot(r, history[i].cmd) < FirstSlot(r, history[j].cmd)

Linearizability ==
    /\ AckMatches
    /\ ReadsConsistent
    /\ RealTimeOrder
    /\ ResultsAgree

Safety ==
    /\ TypeOK
    /\ QuorumIntersection
    /\ ChosenConsistency
    /\ CommittedIsChosen
    /\ CommitAgreement
    /\ VotesBelowBallot
    /\ AcceptPreservesChosen
    /\ LeaderPreservesVotes
    /\ Linearizability

-----------------------------------------------------------------------------
(* Liveness *)

\* Every submitted request is eventually acknowledged
RequestsEventuallyAcked ==
    \A c \in Commands : (c \in submitted) ~> (c \in acked)

\* All requests are eventually acknowledged
AllAcked == <>(acked = Commands)

THEOREM Spec => []Safety
=============================================================================
```