```tla
Accept(a, m) ==
  /\ m \in msgs
  /\ CanAccept(a, m)
  /\ maxBal'  = [maxBal  EXCEPT ![a][m.slot] = m.bal]
  /\ maxVBal' = [maxVBal EXCEPT ![a][m.slot] = m.bal]
  /\ maxVal'  = [maxVal  EXCEPT ![a][m.slot] = m.val]
  /\ votes'   = [votes   EXCEPT ![a] = @ \cup {<<m.slot, m.bal, m.val>>}]
  /\ msgs'    = msgs \cup {[type |-> "2b", slot |-> m.slot, bal |-> m.bal,
                            val |-> m.val, acc |-> a]}
  /\ UNCHANGED <<proposerVars, decided>>

\* Reject a stale prepare or accept request and tell the proposer.
Reject(a, m) ==
  /\ m \in msgs
  /\ CanReject(a, m)
  /\ msgs' = msgs \cup {NackMsg(a, m)}
  /\ UNCHANGED <<acceptorVars, proposerVars, votes, decided>>

AcceptorAction(a) ==
  \E m \in msgs : Promise(a, m) \/ Accept(a, m) \/ Reject(a, m)

-----------------------------------------------------------------------------
(* Learning and the environment                                            *)

\* A value is decided for slot s once a majority accepted it in the same ballot.
Learn(s) ==
  /\ decided[s] = None
  /\ \E b \in Ballots, v \in Values :
        /\ LearnableIn(s, b, v)
        /\ decided' = [decided EXCEPT ![s] = v]
  /\ UNCHANGED <<acceptorVars, msgs, proposerVars, votes>>

\* Message loss.
Lose(m) ==
  /\ m \in msgs
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<acceptorVars, proposerVars, votes, decided>>

LossStep == \E m \in msgs : Lose(m)

Next ==
  \/ \E p \in Proposers : ProposerAction(p)
  \/ \E a \in Acceptors : AcceptorAction(a)
  \/ \E s \in Slots : Learn(s)
  \/ LossStep

Spec == Init /\ [][Next]_vars

\* Weak fairness for the eventual sole proposer, all acceptors, and learning.
\* WF is enough: once loss stops, these actions stay enabled until they are taken.
FairSpec ==
  /\ Spec
  /\ \A s \in Slots :
        /\ WF_vars(\E b \in Ballots : Prepare(Leader, s, b))
        /\ WF_vars(\E v \in Values : Phase2a(Leader, s, v))
        /\ WF_vars(Timeout(Leader, s))
        /\ WF_vars(Learn(s))
  /\ WF_vars(\E m \in msgs : ReceivePromise(Leader, m) \/ ReceiveNack(Leader, m))
  /\ \A a \in Acceptors : WF_vars(AcceptorAction(a))

-----------------------------------------------------------------------------
(* Safety definitions                                                      *)

VotedFor(a, s, b, v) == <<s, b, v>> \in votes[a]

ChosenIn(s, b, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, s, b, v)

Chosen(s, v) == \E b \in Ballots : ChosenIn(s, b, v)

\* Acceptor a has not voted in ballot c, and never will.
WontVoteIn(a, s, c) ==
  /\ \A w \in Values : ~ VotedFor(a, s, c, w)
  /\ maxBal[a][s] > c

\* No value other than v has been or can be chosen in any ballot below b.
SafeAt(s, b, v) ==
  \A c \in Ballots :
     c < b => \E Q \in Quorums : \A a \in Q : VotedFor(a, s, c, v) \/ WontVoteIn(a, s, c)

-----------------------------------------------------------------------------
(* Safety invariants                                                       *)

\* No two different values are chosen for the same slot.
Agreement ==
  \A s \in Slots, v1, v2 \in Values : Chosen(s, v1) /\ Chosen(s, v2) => v1 = v2

\* Any decided value was accepted by a majority in a single ballot.
DecidedWasChosen ==
  \A s \in Slots : decided[s] # None => Chosen(s, decided[s])

\* A decided value is the only value that can ever be chosen in its slot.
DecidedAgreement ==
  \A s \in Slots, v \in Values :
     decided[s] # None /\ Chosen(s, v) => v = decided[s]

\* An acceptor's accepted ballot never exceeds its promise.
\* Every recorded vote is no higher than the current promise.
PromiseRespected ==
  \A a \in Acceptors, s \in Slots :
     /\ maxVBal[a][s] <= maxBal[a][s]
     /\ \A b \in Ballots, v \in Values : VotedFor(a, s, b, v) => b <= maxBal[a][s]

\* The persistent last-accepted pair matches an actual accept.
\* It is the highest accept for that slot.
AcceptedStateConsistent ==
  \A a \in Acceptors, s \in Slots :
     /\ (maxVBal[a][s] = NoBal) <=> (maxVal[a][s] = None)
     /\ maxVBal[a][s] # NoBal => VotedFor(a, s, maxVBal[a][s], maxVal[a][s])
     /\ \A b \in Ballots, v \in Values : VotedFor(a, s, b, v) => b <= maxVBal[a][s]

\* Within one ballot of one slot, at most one value is ever accepted.
OneValuePerBallot ==
  \A a1, a2 \in Acceptors, s \in Slots, b \in Ballots, v1, v2 \in Values :
     VotedFor(a1, s, b, v1) /\ VotedFor(a2, s, b, v2) => v1 = v2

\* Every accepted vote is safe.
VotesSafe ==
  \A a \in Acceptors, s \in Slots, b \in Ballots, v \in Values :
     VotedFor(a, s, b, v) => SafeAt(s, b, v)
```