------------------------------ MODULE NBAC ------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N, Mode

ASSUME N \in Nat \ {0}
ASSUME Mode \in {"Arbitrary", "AllYES", "AllNO"}

(*
  Processes and basic domains
*)
Proc == 1..N
VoteVal == {"YES", "NO"}
Unknown == "UNKNOWN"
OptionVote == VoteVal \cup {Unknown}
DecisionVal == {"UNDECIDED", "COMMIT", "ABORT"}

VARIABLES
  Votes,       \* [Proc -> VoteVal]
  Crashed,     \* SUBSET Proc
  Sent,        \* SUBSET (Proc \X Proc), pairs <<p,q>> where p sent to q
  Msgs,        \* SUBSET of records [from: Proc, to: Proc, val: VoteVal]
  Received,    \* [Proc -> [Proc -> OptionVote]]
  Decision,    \* [Proc -> DecisionVal]
  Suspected    \* SUBSET Proc

vars == << Votes, Crashed, Sent, Msgs, Received, Decision, Suspected >>

TypeInv ==
  /\ Votes \in [Proc -> VoteVal]
  /\ Crashed \subseteq Proc
  /\ Sent \subseteq (Proc \X Proc)
  /\ Msgs \subseteq [from: Proc, to: Proc, val: VoteVal]
  /\ Received \in [Proc -> [Proc -> OptionVote]]
  /\ Decision \in [Proc -> DecisionVal]
  /\ Suspected \subseteq Proc

VotesOk ==
  IF Mode = "Arbitrary" THEN Votes \in [Proc -> VoteVal]
  ELSE IF Mode = "AllYES" THEN Votes = [p \in Proc |-> "YES"]
  ELSE IF Mode = "AllNO" THEN Votes = [p \in Proc |-> "NO"]
  ELSE FALSE

Init ==
  /\ VotesOk
  /\ Crashed = {}
  /\ Sent = {}
  /\ Msgs = {}
  /\ Suspected = {}
  /\ Received = [p \in Proc |->
                   [q \in Proc |->
                      IF q = p THEN Votes[p] ELSE Unknown]]
  /\ Decision = [p \in Proc |-> "UNDECIDED"]
  /\ TypeInv

BroadcastDone(p) == \A q \in Proc: q = p \/ <<p,q>> \in Sent

CanCommit(p) ==
  /\ Suspected = {}
  /\ \A q \in Proc: Received[p][q] = "YES"

MustAbort(p) ==
  \/ Suspected # {}
  \/ \E q \in Proc: Received[p][q] = "NO"

Send(p, q) ==
  /\ p \in Proc /\ q \in Proc /\ p # q
  /\ p \notin Crashed
  /\ <<p,q>> \notin Sent
  /\ Sent' = Sent \cup {<<p,q>>}
  /\ Msgs' = Msgs \cup {[from |-> p, to |-> q, val |-> Votes[p]]}
  /\ UNCHANGED << Votes, Crashed, Received, Decision, Suspected >>

Receive(p, q) ==
  /\ p \in Proc /\ q \in Proc /\ p # q
  /\ p \notin Crashed
  /\ \E m \in Msgs: m.from = q /\ m.to = p
  /\ LET m == CHOOSE mm \in Msgs: mm.from = q /\ mm.to = p
     IN
       /\ Msgs' = Msgs \ {m}
       /\ Received' = [Received EXCEPT ![p][q] = m.val]
       /\ UNCHANGED << Votes, Crashed, Sent, Decision, Suspected >>

DecideCommit(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ Decision[p] = "UNDECIDED"
  /\ BroadcastDone(p)
  /\ CanCommit(p)
  /\ Decision' = [Decision EXCEPT ![p] = "COMMIT"]
  /\ UNCHANGED << Votes, Crashed, Sent, Msgs, Received, Suspected >>

DecideAbort(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ Decision[p] = "UNDECIDED"
  /\ BroadcastDone(p)
  /\ MustAbort(p)
  /\ Decision' = [Decision EXCEPT ![p] = "ABORT"]
  /\ UNCHANGED << Votes, Crashed, Sent, Msgs, Received, Suspected >>

Crash(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ Crashed' = Crashed \cup {p}
  /\ UNCHANGED << Votes, Sent, Msgs, Received, Decision, Suspected >>

SuspectAdd ==
  /\ \E r \in Proc \ Suspected: TRUE
  /\ LET r == CHOOSE x \in Proc \ Suspected: TRUE
     IN
       /\ Suspected' = Suspected \cup {r}
       /\ UNCHANGED << Votes, Crashed, Sent, Msgs, Received, Decision >>

SuspectRemove ==
  /\ \E r \in Suspected: TRUE
  /\ LET r == CHOOSE x \in Suspected: TRUE
     IN
       /\ Suspected' = Suspected \ {r}
       /\ UNCHANGED << Votes, Crashed, Sent, Msgs, Received, Decision >>

Next ==
  \/ \E p \in Proc, q \in Proc: Send(p, q)
  \/ \E p \in Proc, q \in Proc: Receive(p, q)
  \/ \E p \in Proc: DecideCommit(p)
  \/ \E p \in Proc: DecideAbort(p)
  \/ \E p \in Proc: Crash(p)
  \/ SuspectAdd
  \/ SuspectRemove

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

Fairness ==
  /\ \A p \in Proc: \A q \in Proc: WF_vars(Send(p, q))
  /\ \A p \in Proc: \A q \in Proc: WF_vars(Receive(p, q))
  /\ \A p \in Proc: WF_vars(DecideCommit(p))
  /\ \A p \in Proc: WF_vars(DecideAbort(p))

Decided(p) == Decision[p] # "UNDECIDED"

AgreementLocal ==
  \A p \in Proc: \A q \in Proc:
    ~(Decision[p] = "COMMIT" /\ Decision[q] = "ABORT" /\ p \notin Crashed /\ q \notin Crashed)

AgreementSafety == [] AgreementLocal

AbortValidity ==
  (\E r \in Proc: Votes[r] = "NO")
  => [] (\A p \in Proc: Decision[p] # "COMMIT")

CommitValidity ==
  ((\A p \in Proc: Votes[p] = "YES") /\ [] (Suspected = {}))
  => [] (\A p \in Proc: Decision[p] # "ABORT")

Termination ==
  ([] (Crashed = {}) /\ [] (Suspected = {}))
  => []<>(\A p \in Proc: Decided(p))

=============================================================================