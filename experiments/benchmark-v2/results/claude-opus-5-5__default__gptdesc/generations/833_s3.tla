s \cup {[type |-> "Prepare", src |-> r, bal |-> bmin]}
          /\ UNCHANGED <<pending, observed>>

HandlePrepare(r) ==
    \E m \in msgs :
        /\ m.type = "Prepare"
        /\ m.bal >= node[r].balMaxKnown
        /\ ~ \E m2 \in msgs : /\ m2.type = "PrepareReply"
                              /\ m2.src = r
                              /\ m2.bal = m.bal
        /\ node' = [node EXCEPT ![r].leader = m.src,
                                ![r].balMaxKnown = m.bal,
                                ![r].balPrepared = IF m.src = r THEN @ ELSE 0]
        /\ msgs' = msgs \cup {[type  |-> "PrepareReply",
                               src   |-> r,
                               bal   |-> m.bal,
                               voted |-> [s \in Slots |-> node[r].insts[s].voted]]}
        /\ UNCHANGED <<pending, observed>>

PrepareReplies(b) == {m \in msgs : m.type = "PrepareReply" /\ m.bal = b}

SlotVotes(b, s) == {m.voted[s] : m \in PrepareReplies(b)} \ {[bal |-> 0, cmd |-> "nil"]}

Adopted(b, s) ==
    IF SlotVotes(b, s) = {} THEN "nil"
    ELSE (CHOOSE v \in SlotVotes(b, s) : \A w \in SlotVotes(b, s) : w.bal <= v.bal).cmd

MaxUsedSlot(r, b) ==
    SetMax({s \in Slots : Adopted(b, s) # "nil" \/ node[r].insts[s].status = "Committed"} \cup {0})

PreparedInsts(r, b) ==
    [s \in Slots |->
        IF node[r].insts[s].status = "Committed" THEN node[r].insts[s]
        ELSE IF Adopted(b, s) # "nil"
             THEN [status |-> "Accepting", cmd |-> Adopted(b, s), voted |-> node[r].insts[s].voted]
        ELSE IF s <= MaxUsedSlot(r, b)
             THEN [status |-> "Accepting", cmd |-> "nop", voted |-> node[r].insts[s].voted]
        ELSE [status |-> "Empty", cmd |-> "nil", voted |-> node[r].insts[s].voted]]

HandlePrepareReplies(r) ==
    LET b == node[r].balMaxKnown IN
    /\ node[r].leader = r
    /\ b > 0
    /\ node[r].balPrepared # b
    /\ Cardinality({m.src : m \in PrepareReplies(b)}) >= MajorityNum
    /\ LET newInsts == PreparedInsts(r, b) IN
       /\ node' = [node EXCEPT ![r].balPrepared = b,
                               ![r].insts = newInsts]
       /\ msgs' = msgs \cup
                  {[type |-> "Accept", src |-> r, bal |-> b, slot |-> s, cmd |-> newInsts[s].cmd] :
                       s \in {x \in Slots : newInsts[x].status = "Accepting"}}
    /\ UNCHANGED <<pending, observed>>

ProposeCommand(r) ==
    /\ IsActiveLeader(r)
    /\ \E s \in Slots : node[r].insts[s].status = "Empty"
    /\ \E c \in pending :
        /\ c \notin {node[r].insts[x].cmd : x \in Slots}
        /\ LET s == CHOOSE x \in Slots :
                       /\ node[r].insts[x].status = "Empty"
                       /\ \A y \in 1..(x - 1) : node[r].insts[y].status # "Empty"
               b == node[r].balMaxKnown
           IN /\ node' = [node EXCEPT ![r].insts[s] =
                             [status |-> "Accepting", cmd |-> c, voted |-> @.voted]]
              /\ msgs' = msgs \cup {[type |-> "Accept", src |-> r, bal |-> b, slot |-> s, cmd |-> c]}
    /\ UNCHANGED <<pending, observed>>

HandleAccept(r) ==
    \E m \in msgs :
        /\ m.type = "Accept"
        /\ m.bal >= node[r].balMaxKnown
        /\ ~ \E m2 \in msgs : /\ m2.type = "AcceptReply"
                              /\ m2.src = r
                              /\ m2.bal = m.bal
                              /\ m2.slot = m.slot
        /\ node' = [node EXCEPT
                      ![r].leader = m.src,
                      ![r].balMaxKnown = m.bal,
                      ![r].balPrepared = IF m.src = r THEN @ ELSE 0,
                      ![r].insts[m.slot] =
                          IF @.status = "Committed"
                          THEN [@ EXCEPT !.voted = [bal |-> m.bal, cmd |-> m.cmd]]
                          ELSE [status |-> "Accepting", cmd |-> m.cmd,
                                voted |-> [bal |-> m.bal, cmd |-> m.cmd]]]
        /\ msgs' = msgs \cup {[type |-> "AcceptReply", src |-> r, bal |-> m.bal, slot |-> m.slot]}
        /\ UNCHANGED <<pending, observed>>

AcceptRepliers(b, s) ==
    {m.src : m \in {x \in msgs : x.type = "AcceptReply" /\ x.bal = b /\ x.slot = s}}

HandleAcceptReplies(r) ==
    /\ IsActiveLeader(r)
    /\ \E s \in Slots :
        /\ node[r].insts[s].status = "Accepting"
        /\ Cardinality(AcceptRepliers(node[r].balMaxKnown, s)) >= MajorityNum
        /\ node' = [node EXCEPT ![r].insts[s].status = "Committed"]
        /\ msgs' = msgs \cup {[type |-> "CommitNotice", slot |-> s, cmd |-> node[r].insts[s].cmd]}
    /\ UNCHANGED <<pending, observed>>

HandleCommitNotice(r) ==
    \E m \in msgs :
        /\ m.type = "CommitNotice"
        /\ node[r].insts[m.slot].status # "Committed"
        /\ node' = [node EXCEPT ![r].insts[m.slot] =
                       [status |-> "Committed", cmd |-> m.cmd, voted |-> @.voted]]
        /\ UNCHANGED <<msgs, pending, observed>>

Execute(r) ==
    LET s == node[r].commitUpTo + 1 IN
    /\ s \in Slots
    /\ node[r].insts[s].status = "Committed"
    /\ LET c   == node[r].insts[s].cmd
           dup == \/ c = "nop"
                  \/ \E s2 \in 1..(s - 1) : node[r].insts[s2].cmd = c
       IN /\ node' = [node EXCEPT
                        ![r].commitUpTo = s,
                        ![r].kvalue = IF ~dup /\ c \in Writes THEN c ELSE @]
          /\ IF ~dup /\ c \notin Acked
             THEN /\ observed' = Append(observed,
                        AckEvent(c, IF c \in Writes THEN c ELSE node[r].kvalue))
                  /\ pending' = pending \ {c}
             ELSE UNCHANGED <<observed, pending>>
    /\ UNCHANGED msgs

Terminating == AllAcked /\ UNCHANGED vars

Next == \/ ClientRequest
        \/ \E r \in Replicas :
              \/ BecomeLeader(r)
              \/ HandlePrepare(r)
              \/ HandlePrepareReplies(r)
              \/ ProposeCommand(r)
              \/ HandleAccept(r)
              \/ HandleAcceptReplies(r)
              \/ HandleCommitNotice(r)
              \/ Execute(r)
        \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

ConsensusSafety ==
    \A r1, r2 \in Replicas : \A s \in Slots :
        (node[r1].insts[s].status = "Committed" /\ node[r2].insts[s].status = "Committed")
            => node[r1].insts[s].cmd = node[r2].insts[s].cmd

ReqIdx(c) == CHOOSE i \in DOMAIN observed : observed[i].type = "Req" /\ observed[i].cmd = c
AckIdx(c) == CHOOSE i \in AckIdxs : observed[i].cmd = c
AckVal(c) == observed[AckIdx(c)].val

NumAcked == Cardinality(Acked)

Orders == {f \in [1..NumAcked -> Acked] : \A i, j \in 1..NumAcked : i # j => f[i] # f[j]}

LastWrite(f, k) ==
    LET ws == {j \in 1..(k - 1) : f[j] \in Writes}
    IN IF ws = {} THEN "nil" ELSE f[SetMax(ws)]

ValidOrder(f) ==
    /\ \A i, j \in 1..NumAcked : AckIdx(f[i]) < ReqIdx(f[j]) => i < j
    /\ \A k \in 1..NumAcked : f[k] \in Reads => AckVal(f[k]) = LastWrite(f, k)
    /\ \A k \in 1..NumAcked : f[k] \in Writes => AckVal(f[k]) = f[k]

Linearizability == \E f \in Orders : ValidOrder(f)

AckedWereRequested == \A c \in Acked : c \in Requested /\ ReqIdx(c) < AckIdx(c)

Liveness == <>AllAcked

====