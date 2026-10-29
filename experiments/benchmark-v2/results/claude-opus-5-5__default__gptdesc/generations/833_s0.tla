```tla
 b,
                      slot |-> s, cmd |-> newInst(s).cmd] :
                     s \in {t \in Slots : newInst(t).status = "Accepting"}})
        /\ UNCHANGED clientVars

(* Prepared leader r puts a requested command into the lowest empty slot *)

TakeRequest(r, c) ==
    LET b == node[r].balMaxKnown IN
    /\ b > 0
    /\ BallotOwner(b) = r
    /\ node[r].balPrepared = b
    /\ c \in reqsMade
    /\ c \notin acked
    /\ \A s \in Slots : node[r].insts[s].cmd # c
    /\ \E s \in Slots :
        /\ node[r].insts[s].status = "Empty"
        /\ \A t \in Slots : t < s => node[r].insts[t].status # "Empty"
        /\ node' = [node EXCEPT ![r].insts[s] =
                        [status |-> "Accepting", cmd |-> c,
                         voted  |-> node[r].insts[s].voted]]
        /\ Send([type |-> "Accept", src |-> r, bal |-> b, slot |-> s, cmd |-> c])
    /\ UNCHANGED clientVars

(* Replica r handles an Accept message *)

HandleAccept(r) ==
    \E m \in msgs :
        /\ m.type = "Accept"
        /\ m.bal >= node[r].balMaxKnown
        /\ node[r].insts[m.slot].voted # [bal |-> m.bal, cmd |-> m.cmd]
        /\ node' = [node EXCEPT
                       ![r].leader      = BallotOwner(m.bal),
                       ![r].balMaxKnown = m.bal,
                       ![r].balPrepared = IF m.bal = node[r].balPrepared
                                          THEN m.bal ELSE 0,
                       ![r].insts[m.slot].voted = [bal |-> m.bal, cmd |-> m.cmd]]
        /\ Send([type |-> "AcceptReply", src |-> r, bal |-> m.bal, slot |-> m.slot])
        /\ UNCHANGED clientVars

(* Leader r commits a slot when a majority has accepted it *)

HandleAcceptReplies(r) ==
    LET b == node[r].balMaxKnown IN
    /\ b > 0
    /\ BallotOwner(b) = r
    /\ node[r].balPrepared = b
    /\ \E s \in Slots :
        /\ node[r].insts[s].status = "Accepting"
        /\ \E Q \in Quorums :
              \A q \in Q :
                 [type |-> "AcceptReply", src |-> q, bal |-> b, slot |-> s] \in msgs
        /\ node' = [node EXCEPT ![r].insts[s].status = "Committed"]
    /\ UNCHANGED <<msgs>>
    /\ UNCHANGED clientVars

(* Idempotent execution: only the first occurrence of a command counts *)

FirstOccurrence(insts, t) ==
    \A u \in 1..(t - 1) : insts[u].cmd # insts[t].cmd

ReadResult(insts, s) ==
    LET ws == {t \in 1..(s - 1) : /\ insts[t].cmd \in Writes
                                  /\ FirstOccurrence(insts, t)}
    IN IF ws = {} THEN "nil" ELSE insts[Max(ws)].cmd

(* Replica r executes a committed log prefix and acknowledges a command *)

ReplyClient(r) ==
    \E s \in Slots :
        LET c == node[r].insts[s].cmd IN
        /\ \A t \in 1..s : node[r].insts[t].status = "Committed"
        /\ c \in reqsMade
        /\ c \notin acked
        /\ FirstOccurrence(node[r].insts, s)
        /\ acked' = acked \cup {c}
        /\ observed' = Append(observed,
                              AckEvent(c, IF c \in Writes
                                          THEN c
                                          ELSE ReadResult(node[r].insts, s)))
        /\ UNCHANGED <<msgs, node, reqsMade>>

-----------------------------------------------------------------------------
(* Termination and the next-state relation *)

terminated == Len(observed) = 2 * NumCommands

\* Stuttering after termination, so only a pre-termination stop is a deadlock.
Terminating == terminated /\ UNCHANGED vars

Next ==
    \/ \E c \in Commands : ClientRequest(c)
    \/ \E r \in Replicas : \E b \in Ballots : BecomePrepare(r, b)
    \/ \E r \in Replicas : HandlePrepare(r)
    \/ \E r \in Replicas : HandlePrepareReplies(r)
    \/ \E r \in Replicas : \E c \in Commands : TakeRequest(r, c)
    \/ \E r \in Replicas : HandleAccept(r)
    \/ \E r \in Replicas : HandleAcceptReplies(r)
    \/ \E r \in Replicas : ReplyClient(r)
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: committed slots agree across replicas *)

CommittedConsistency ==
    \A r1, r2 \in Replicas : \A s \in Slots :
        (/\ node[r1].insts[s].status = "Committed"
         /\ node[r2].insts[s].status = "Committed")
        => node[r1].insts[s].cmd = node[r2].insts[s].cmd

(* Safety: linearizability from the client's view *)

ReqPos(c) == CHOOSE i \in 1..Len(observed) :
                 observed[i].type = "Req" /\ observed[i].cmd = c
AckPos(c) == CHOOSE i \in 1..Len(observed) :
                 observed[i].type = "Ack" /\ observed[i].cmd = c
AckVal(c) == observed[AckPos(c)].val

Orders == {o \in [1..NumCommands -> Commands] :
              \A c \in Commands : \E i \in 1..NumCommands : o[i] = c}

PosIn(o, c) == CHOOSE i \in 1..NumCommands : o[i] = c

ObeysRealTime(o) ==
    \A c1, c2 \in Commands :
        AckPos(c1) < ReqPos(c2) => PosIn(o, c1) < PosIn(o, c2)

LastWriteBefore(o, i) ==
    LET ws == {j \in 1..(i - 1) : o[j] \in Writes}
    IN IF ws = {} THEN "nil" ELSE o[Max(ws)]

ReadsCorrect(o) ==
    \A i \in 1..NumCommands :
        o[i] \in Reads => AckVal(o[i]) = LastWriteBefore(o, i)

Linearizability ==
    terminated =>
        \E o \in Orders : ObeysRealTime(o) /\ ReadsCorrect(o)

(* Liveness: eventually all requests are observed *)

Liveness == <>terminated

THEOREM Spec => [](TypeOK /\ CommittedConsistency /\ Linearizability)
=============================================================================
```