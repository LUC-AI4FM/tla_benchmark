, cmd : Commands] \cup
                      [type : {"Ack"}, cmd : Commands, val : Writes \cup {NIL}])
  /\ \A r \in Replicas :
       /\ node[r].balPrepared \in 0..MaxBallot
       /\ node[r].balMaxKnown \in 0..MaxBallot
       /\ node[r].execUpTo \in 0..Cardinality(Slots)
       /\ node[r].kvalue \in Writes \cup {NIL}
       /\ \A s \in Slots : node[r].insts[s].status \in Statuses

Init ==
  /\ msgs = {}
  /\ node = [r \in Replicas |->
               [leader      |-> NIL,
                balPrepared |-> 0,
                balMaxKnown |-> 0,
                insts       |-> [s \in Slots |-> EmptyInst],
                execUpTo    |-> 0,
                kvalue      |-> NIL]]
  /\ pending = Commands
  /\ observed = <<>>

IsLeader(r) == /\ node[r].leader = r
               /\ node[r].balPrepared > 0
               /\ node[r].balPrepared = node[r].balMaxKnown

FirstEmpty(r) ==
  CHOOSE s \in Slots :
    /\ node[r].insts[s].status = "Empty"
    /\ \A t \in Slots : t < s => node[r].insts[t].status # "Empty"

AcceptMsg(r, b, s, c)      == [type |-> "Accept", src |-> r, bal |-> b, slot |-> s, cmd |-> c]
AcceptReplyMsg(r, b, s, c) == [type |-> "AcceptReply", src |-> r, bal |-> b, slot |-> s, cmd |-> c]

(* Leader election: replica r proposes a fresh ballot b *)
Prepare(r, b) ==
  /\ b > node[r].balMaxKnown
  /\ ~\E m \in msgs : m.type = "Prepare" /\ m.bal = b
  /\ node' = [node EXCEPT ![r].leader = r,
                          ![r].balPrepared = 0,
                          ![r].balMaxKnown = b]
  /\ msgs' = msgs \cup
       { [type |-> "Prepare", src |-> r, bal |-> b],
         [type |-> "PrepareReply", src |-> r, bal |-> b,
          voted |-> [s \in Slots |-> node[r].insts[s].voted]] }
  /\ UNCHANGED <<pending, observed>>

HandlePrepare(r, m) ==
  /\ m.type = "Prepare"
  /\ m.bal > node[r].balMaxKnown
  /\ node' = [node EXCEPT ![r].leader = m.src,
                          ![r].balPrepared = 0,
                          ![r].balMaxKnown = m.bal]
  /\ msgs' = msgs \cup
       { [type |-> "PrepareReply", src |-> r, bal |-> m.bal,
          voted |-> [s \in Slots |-> node[r].insts[s].voted]] }
  /\ UNCHANGED <<pending, observed>>

(* Leader gathers majority of prepare replies and recovers in-progress slots *)
BecomeLeader(r) ==
  LET b == node[r].balMaxKnown
      Q == {m \in msgs : m.type = "PrepareReply" /\ m.bal = b}
      Votes(s) == {v \in {m.voted[s] : m \in Q} : v.bal > 0}
      MaxVote(s) == CHOOSE v \in Votes(s) : \A w \in Votes(s) : w.bal <= v.bal
      Known(s) == node[r].insts[s].status = "Committed" \/ Votes(s) # {}
      Hi == IF \E s \in Slots : Known(s)
              THEN CHOOSE s \in Slots : Known(s) /\ \A t \in Slots : Known(t) => t <= s
              ELSE 0
      NewInst(s) ==
        IF node[r].insts[s].status = "Committed" THEN node[r].insts[s]
        ELSE IF Votes(s) # {}
          THEN [status |-> "Accepting", cmd |-> MaxVote(s).cmd,
                voted |-> [bal |-> b, cmd |-> MaxVote(s).cmd]]
        ELSE IF s < Hi
          THEN [status |-> "Accepting", cmd |-> NOP,
                voted |-> [bal |-> b, cmd |-> NOP]]
        ELSE [status |-> "Empty", cmd |-> NIL, voted |-> node[r].insts[s].voted]
      NewInsts == [s \in Slots |-> NewInst(s)]
      Reproposed == {s \in Slots : NewInsts[s].status = "Accepting"}
  IN
  /\ node[r].leader = r
  /\ node[r].balPrepared = 0
  /\ b > 0
  /\ Cardinality({m.src : m \in Q}) >= MajorityNum
  /\ node' = [node EXCEPT ![r].balPrepared = b, ![r].insts = NewInsts]
  /\ msgs' = msgs \cup {AcceptMsg(r, b, s, NewInsts[s].cmd) : s \in Reproposed}
                  \cup {AcceptReplyMsg(r, b, s, NewInsts[s].cmd) : s \in Reproposed}
  /\ UNCHANGED <<pending, observed>>

(* Leader takes a new client request (or retries an in-flight lost one) *)
TakeCommand(r, c) ==
  /\ IsLeader(r)
  /\ \E s \in Slots : node[r].insts[s].status = "Empty"
  /\ \/ /\ c \in pending
        /\ pending' = pending \ {c}
        /\ observed' = Append(observed, ReqEvent(c))
     \/ /\ c \notin pending
        /\ Requested(c)
        /\ ~Acked(c)
        /\ \A t \in Slots : node[r].insts[t].cmd # c
        /\ UNCHANGED <<pending, observed>>
  /\ LET s == FirstEmpty(r)
         b == node[r].balPrepared
     IN /\ node' = [node EXCEPT ![r].insts[s] =
                      [status |-> "Accepting", cmd |-> c,
                       voted |-> [bal |-> b, cmd |-> c]]]
        /\ msgs' = msgs \cup {AcceptMsg(r, b, s, c), AcceptReplyMsg(r, b, s, c)}

HandleAccept(r, m) ==
  /\ m.type = "Accept"
  /\ m.src # r
  /\ m.bal >= node[r].balMaxKnown
  /\ node[r].insts[m.slot].voted # [bal |-> m.bal, cmd |-> m.cmd]
  /\ LET old == node[r].insts[m.slot]
         isC == old.status = "Committed"
     IN node' = [node EXCEPT
                   ![r].leader = m.src,
                   ![r].balMaxKnown = m.bal,
                   ![r].balPrepared = 0,
                   ![r].insts[m.slot] =
                      [status |-> IF isC THEN "Committed" ELSE "Accepting",
                       cmd    |-> IF isC THEN old.cmd ELSE m.cmd,
                       voted  |-> [bal |-> m.bal, cmd |-> m.cmd]]]
  /\ msgs' = msgs \cup {AcceptReplyMsg(r, m.bal, m.slot, m.cmd)}
  /\ UNCHANGED <<pending, observed>>

(* Leader commits a slot accepted by a majority at its ballot *)
Commit(r, s) ==
  LET b == node[r].balPrepared
      c == node[r].insts[s].cmd
  IN
  /\ IsLeader(r)
  /\ node[r].insts[s].status = "Accepting"
  /\ node[r].insts[s].voted.bal = b
  /\ Cardinality({m.src : m \in {m2 \in msgs : /\ m2.type = "AcceptReply"
                                              /\ m2.bal = b
                                              /\ m2.slot = s}}) >= MajorityNum
  /\ node' = [node EXCEPT ![r].insts[s].status = "Committed"]
  /\ msgs' = msgs \cup {[type |-> "CommitNotice", slot |-> s, cmd |-> c]}
  /\ UNCHANGED <<pending, observed>>

HandleCommitNotice(r, m) ==
  /\ m.type = "CommitNotice"
  /\ node[r].insts[m.slot].status # "Committed"
  /\ node' = [node EXCEPT ![r].insts[m.slot].status = "Committed",
                          ![r].insts[m.slot].cmd = m.cmd]
  /\ UNCHANGED <<msgs, pending, observed>>

(* Apply the next committed slot; duplicates and no-ops are skipped *)
Execute(r) ==
  LET s   == node[r].execUpTo + 1
      c   == node[r].insts[s].cmd
      old == node[r].kvalue
      dup == c = NOP \/ \E t \in 1..(s - 1) : node[r].insts[t].cmd = c
  IN
  /\ s \in Slots
  /\ node[r].insts[s].status = "Committed"
  /\ node' = [node EXCEPT ![r].execUpTo = s,
                          ![r].kvalue = IF ~dup /\ c \in Writes THEN c ELSE old]
  /\ observed' = IF ~dup /\ ~Acked(c)
                   THEN Append(observed, AckEvent(c, old))
                   ELSE observed
  /\ UNCHANGED <<msgs, pending>>

AllObserved == pending = {} /\ \A c \in Commands : Acked(c)

NonTerminalNext ==
  \/ \E r \in Replicas, b \in Ballots : Prepare(r, b)
  \/ \E r \in Replicas, m \in msgs : HandlePrepare(r, m)
  \/ \E r \in Replicas : BecomeLeader(r)
  \/ \E r \in Replicas, c \in Commands : TakeCommand(r, c)
  \/ \E r \in Replicas, m \in msgs : HandleAccept(r, m)
  \/ \E r \in Replicas, s \in Slots : Commit(r, s)
  \/ \E r \in Replicas, m \in msgs : HandleCommitNotice(r, m)
  \/ \E r \in Replicas : Execute(r)

Done == AllObserved /\ UNCHANGED vars

Next == NonTerminalNext \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(NonTerminalNext)

-----------------------------------------------------------------------------
(* Linearizability *)
ReqIdx(c) == CHOOSE i \in 1..Len(observed) :
               observed[i].type = "Req" /\ observed[i].cmd = c
AckIdx(c) == CHOOSE i \in 1..Len(observed) :
               observed[i].type = "Ack" /\ observed[i].cmd = c
AckVal(c) == observed[AckIdx(c)].val

MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

Orders == {f \in [1..NumCommands -> Commands] :
             \A i, j \in 1..NumCommands : i # j => f[i] # f[j]}

PrevValue(f, i) ==
  LET W == {j \in 1..(i - 1) : f[j] \in Writes}
  IN IF W = {} THEN NIL ELSE f[MaxOf(W)]

Linearizable ==
  \E f \in Orders :
    /\ \A i, j \in 1..NumCommands :
         i < j => ~(AckIdx(f[j]) < ReqIdx(f[i]))
    /\ \A i \in 1..NumCommands : AckVal(f[i]) = PrevValue(f, i)

Linearizability == AllObserved => Linearizable

(* Consensus safety *)
Chosen(s, c) ==
  \E b \in Ballots :
    Cardinality({m.src : m \in {m2 \in msgs : /\ m2.type = "AcceptReply"
                                             /\ m2.bal = b
                                             /\ m2.slot = s
                                             /\ m2.cmd = c}}) >= MajorityNum

ConsensusSafety ==
  \A s \in Slots : \A c1, c2 \in Commands \cup {NOP} :
    Chosen(s, c1) /\ Chosen(s, c2) => c1 = c2

CommittedAgreement ==
  \A r1, r2 \in Replicas : \A s \in Slots :
    (node[r1].insts[s].status = "Committed" /\ node[r2].insts[s].status = "Committed")
      => node[r1].insts[s].cmd = node[r2].insts[s].cmd

(* Deadlock freedom *)
NoDeadlock == AllObserved \/ ENABLED NonTerminalNext

Termination == <>AllObserved

THEOREM Spec => [](TypeOK /\ Linearizability /\ ConsensusSafety /\ CommittedAgreement /\ NoDeadlock)
=============================================================================
```