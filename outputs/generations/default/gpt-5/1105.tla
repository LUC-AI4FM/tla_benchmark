----------------------------- MODULE AtomicCommitFD -----------------------------

EXTENDS Naturals

CONSTANTS
  Proc,          \* Non-empty set of process identifiers
  YES, NO,       \* Vote values
  COMMIT, ABORT, UNDECIDED, \* Decision values
  VOTE, DECIDE,  \* Message kinds
  UNKNOWN,       \* Unknown local knowledge of a vote
  AllYes, AllNo, VMode \* Specialized initial vote mode

ASSUME
  /\ Proc /= {}
  /\ YES /= NO
  /\ COMMIT /= ABORT
  /\ UNDECIDED /= COMMIT
  /\ UNDECIDED /= ABORT
  /\ VOTE /= DECIDE
  /\ AllYes /= AllNo
  /\ VMode \in {AllYes, AllNo}

VARIABLES
  vote,      \* [Proc -> {YES, NO}] fixed initial votes
  msgs,      \* set of messages in transit
  recvd,     \* [Proc -> [Proc -> {YES, NO, UNKNOWN}]] local knowledge of votes
  decided,   \* [Proc -> {UNDECIDED, COMMIT, ABORT}]
  sent,      \* [Proc -> BOOLEAN] whether initial vote broadcast was sent
  crashed,   \* [Proc -> BOOLEAN]
  susp       \* [Proc -> SUBSET Proc] per-process suspicion sets

Vars == << vote, msgs, recvd, decided, sent, crashed, susp >>

Message ==
  [ from : Proc,
    to   : Proc,
    kind : {VOTE, DECIDE},
    val  : {YES, NO, COMMIT, ABORT} ]

VotesFrom(p) ==
  { [from |-> p, to |-> q, kind |-> VOTE,   val |-> vote[p]] : q \in Proc }

DecideMsgs(p, d) ==
  { [from |-> p, to |-> q, kind |-> DECIDE, val |-> d]        : q \in Proc }

VoteInitFun ==
  [ p \in Proc |-> IF VMode = AllYes THEN YES ELSE NO ]

Init ==
  /\ vote = VoteInitFun
  /\ msgs = {}
  /\ recvd = [ p \in Proc |-> [ q \in Proc |-> UNKNOWN ] ]
  /\ decided = [ p \in Proc |-> UNDECIDED ]
  /\ sent = [ p \in Proc |-> FALSE ]
  /\ crashed = [ p \in Proc |-> FALSE ]
  /\ susp = [ p \in Proc |-> {} ]

Crash(p) ==
  /\ ~crashed[p]
  /\ crashed' = [crashed EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, msgs, recvd, decided, sent, susp >>

FDUpdate(p) ==
  /\ ~crashed[p]
  /\ \E S \in SUBSET Proc:
       /\ susp[p] \subseteq S
       /\ susp' = [susp EXCEPT ![p] = S]
  /\ UNCHANGED << vote, msgs, recvd, decided, sent, crashed >>

SendVote(p) ==
  /\ ~crashed[p]
  /\ decided[p] = UNDECIDED
  /\ sent[p] = FALSE
  /\ msgs' = msgs \cup VotesFrom(p)
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, recvd, decided, crashed, susp >>

ReceiveVote(p) ==
  /\ ~crashed[p]
  /\ decided[p] = UNDECIDED
  /\ \E m \in msgs:
       /\ m.to = p
       /\ m.kind = VOTE
       /\ msgs' = msgs \ {m}
       /\ recvd' = [recvd EXCEPT ![p][m.from] = m.val]
  /\ UNCHANGED << vote, decided, sent, crashed, susp >>

DecideAbortByNO(p) ==
  /\ ~crashed[p]
  /\ decided[p] = UNDECIDED
  /\ \E q \in Proc: recvd[p][q] = NO
  /\ decided' = [decided EXCEPT ![p] = ABORT]
  /\ msgs' = msgs \cup DecideMsgs(p, ABORT)
  /\ UNCHANGED << vote, recvd, sent, crashed, susp >>

DecideAbortBySuspect(p) ==
  /\ ~crashed[p]
  /\ decided[p] = UNDECIDED
  /\ susp[p] # {}
  /\ decided' = [decided EXCEPT ![p] = ABORT]
  /\ msgs' = msgs \cup DecideMsgs(p, ABORT)
  /\ UNCHANGED << vote, recvd, sent, crashed, susp >>

DecideCommit(p) ==
  /\ ~crashed[p]
  /\ decided[p] = UNDECIDED
  /\ susp[p] = {}
  /\ \A q \in Proc: recvd[p][q] = YES
  /\ decided' = [decided EXCEPT ![p] = COMMIT]
  /\ msgs' = msgs \cup DecideMsgs(p, COMMIT)
  /\ UNCHANGED << vote, recvd, sent, crashed, susp >>

ReceiveDecision(p) ==
  /\ ~crashed[p]
  /\ \E m \in msgs:
       /\ m.to = p
       /\ m.kind = DECIDE
       /\ msgs' = msgs \ {m}
       /\ decided' = IF decided[p] = UNDECIDED
                     THEN [decided EXCEPT ![p] = m.val]
                     ELSE decided
  /\ UNCHANGED << vote, recvd, sent, crashed, susp >>

ProcStep(p) ==
  SendVote(p)
  \/ ReceiveVote(p)
  \/ ReceiveDecision(p)
  \/ DecideAbortByNO(p)
  \/ DecideAbortBySuspect(p)
  \/ DecideCommit(p)
  \/ FDUpdate(p)
  \/ Crash(p)

Next ==
  \E p \in Proc: ProcStep(p)

Fairness ==
  /\ \A p \in Proc: WF_<<vote, msgs, recvd, decided, sent, crashed, susp>>(SendVote(p))
  /\ \A p \in Proc: WF_<<vote, msgs, recvd, decided, sent, crashed, susp>>(ReceiveVote(p))
  /\ \A p \in Proc: WF_<<vote, msgs, recvd, decided, sent, crashed, susp>>(ReceiveDecision(p))
  /\ \A p \in Proc: WF_<<vote, msgs, recvd, decided, sent, crashed, susp>>(DecideAbortByNO(p))
  /\ \A p \in Proc: WF_<<vote, msgs, recvd, decided, sent, crashed, susp>>(DecideAbortBySuspect(p))
  /\ \A p \in Proc: WF_<<vote, msgs, recvd, decided, sent, crashed, susp>>(DecideCommit(p))

Spec ==
  Init /\ [][Next]_Vars /\ Fairness

TypeInv ==
  /\ vote \in [Proc -> {YES, NO}]
  /\ msgs \subseteq Message
  /\ recvd \in [Proc -> [Proc -> {YES, NO, UNKNOWN}]]
  /\ decided \in [Proc -> {UNDECIDED, COMMIT, ABORT}]
  /\ sent \in [Proc -> BOOLEAN]
  /\ crashed \in [Proc -> BOOLEAN]
  /\ susp \in [Proc -> SUBSET Proc]
  /\ \A m \in msgs:
       /\ (m.kind = VOTE   => m.val \in {YES, NO})
       /\ (m.kind = DECIDE => m.val \in {COMMIT, ABORT})

Agreement ==
  []( \A p \in Proc: \A q \in Proc:
        (decided[p] \in {COMMIT, ABORT} /\ decided[q] \in {COMMIT, ABORT})
        => decided[p] = decided[q] )

AbortValidity ==
  []( (\E p \in Proc: vote[p] = NO) => ~(\E q \in Proc: decided[q] = COMMIT) )

CommitValidity ==
  []( (\E q \in Proc: decided[q] = COMMIT) => (\A p \in Proc: vote[p] = YES) )

Termination ==
  [](\A p \in Proc: ~crashed[p] => <> (decided[p] /= UNDECIDED))

EventualCommit ==
  ( (\A p \in Proc: vote[p] = YES)
    /\ [](\A p \in Proc: ~crashed[p])
    /\ [](\A p \in Proc: susp[p] = {}) )
  => <> (\A p \in Proc: decided[p] = COMMIT)

=============================================================================