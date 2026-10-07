------------------------------ MODULE AtomicCommitFD ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANT Proc

ASSUME Proc # {}

\* Basic value sets
VoteVal == {"YES", "NO"}
DecisionVal == {"Undecided", "Commit", "Abort"}
Unknown == "UNKNOWN"

\* Messages carry votes asynchronously
Msg == [type: {"VOTE"}, from: Proc, to: Proc, val: VoteVal]

\* State variables
VARIABLES
  votes,      \* [Proc -> VoteVal], fixed by Init (all YES or all NO)
  Crashed,    \* SUBSET Proc
  Suspect,    \* [Proc -> SUBSET Proc], per-process suspicion set
  Sent,       \* [Proc -> [Proc -> BOOLEAN]], whether p sent its vote to q
  Net,        \* SUBSET Msg, in-flight messages
  Recv,       \* [Proc -> [Proc -> (VoteVal \cup {Unknown})]], what q knows about p's vote
  decision    \* [Proc -> DecisionVal]

vars == << votes, Crashed, Suspect, Sent, Net, Recv, decision >>

\* Typing and structural invariants
TypeInv ==
  /\ votes \in [Proc -> VoteVal]
  /\ Crashed \subseteq Proc
  /\ Suspect \in [Proc -> SUBSET Proc]
  /\ Sent \in [Proc -> [Proc -> BOOLEAN]]
  /\ Net \subseteq Msg
  /\ Recv \in [Proc -> [Proc -> (VoteVal \cup {Unknown})]]
  /\ decision \in [Proc -> DecisionVal]
  /\ \A p \in Proc: Recv[p][p] = votes[p]
  /\ \A p \in Proc: \A q \in Proc: Sent[p][q] \in BOOLEAN

\* Helper predicates over votes and decisions
AllYes == \A p \in Proc: votes[p] = "YES"
SomeNo == \E p \in Proc: votes[p] = "NO"
AllCommit == \A p \in Proc: decision[p] = "Commit"
AllAbort == \A p \in Proc: decision[p] = "Abort"
AllDecided == \A p \in Proc: decision[p] # "Undecided"

\* Specialized initial conditions: either all YES or all NO
InitAllYes ==
  /\ votes = [p \in Proc |-> "YES"]
  /\ Crashed = {}
  /\ Suspect = [p \in Proc |-> {}]
  /\ Sent = [p \in Proc |-> [q \in Proc |-> FALSE]]
  /\ Net = {}
  /\ Recv = [q \in Proc |-> [r \in Proc |-> IF q = r THEN "YES" ELSE Unknown]]
  /\ decision = [p \in Proc |-> "Undecided"]

InitAllNo ==
  /\ votes = [p \in Proc |-> "NO"]
  /\ Crashed = {}
  /\ Suspect = [p \in Proc |-> {}]
  /\ Sent = [p \in Proc |-> [q \in Proc |-> FALSE]]
  /\ Net = {}
  /\ Recv = [q \in Proc |-> [r \in Proc |-> IF q = r THEN "NO" ELSE Unknown]]
  /\ decision = [p \in Proc |-> "Undecided"]

Init == InitAllYes \/ InitAllNo

\* Actions

SendVote(p, q) ==
  /\ p \in Proc /\ q \in Proc
  /\ p \notin Crashed
  /\ ~ Sent[p][q]
  /\ Sent' = [Sent EXCEPT ![p][q] = TRUE]
  /\ Net' = Net \cup { [type |-> "VOTE", from |-> p, to |-> q, val |-> votes[p]] }
  /\ UNCHANGED << votes, Crashed, Suspect, Recv, decision >>

Deliver(m) ==
  /\ m \in Net
  /\ Net' = Net \ {m}
  /\ Recv' = [Recv EXCEPT ![m.to][m.from] = m.val]
  /\ UNCHANGED << votes, Crashed, Suspect, Sent, decision >>

DecideAbort(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ decision[p] = "Undecided"
  /\ ( \E r \in Proc: Recv[p][r] = "NO"
     \/ \E r \in Proc: /\ r \in Suspect[p]
                        /\ Recv[p][r] = Unknown )
  /\ decision' = [decision EXCEPT ![p] = "Abort"]
  /\ UNCHANGED << votes, Crashed, Suspect, Sent, Net, Recv >>

DecideCommit(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ decision[p] = "Undecided"
  /\ \A r \in Proc: Recv[p][r] = "YES"
  /\ Crashed = {}
  /\ decision' = [decision EXCEPT ![p] = "Commit"]
  /\ UNCHANGED << votes, Crashed, Suspect, Sent, Net, Recv >>

CrashProc(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ Crashed' = Crashed \cup {p}
  /\ UNCHANGED << votes, Suspect, Sent, Net, Recv, decision >>

SuspectAdd(q, p) ==
  /\ q \in Proc /\ p \in Proc
  /\ q \notin Crashed
  /\ p \notin Suspect[q]
  /\ Suspect' = [Suspect EXCEPT ![q] = @ \cup {p}]
  /\ UNCHANGED << votes, Crashed, Sent, Net, Recv, decision >>

Next ==
  \/ \E p \in Proc: \E q \in Proc: SendVote(p, q)
  \/ \E m \in Net: Deliver(m)
  \/ \E p \in Proc: DecideAbort(p)
  \/ \E p \in Proc: DecideCommit(p)
  \/ \E p \in Proc: CrashProc(p)
  \/ \E q \in Proc: \E p \in Proc: SuspectAdd(q, p)

\* Weak fairness for non-stuttering process actions
Fair ==
  /\ \A p \in Proc: \A q \in Proc: WF_vars(SendVote(p, q))
  /\ \A p \in Proc: WF_vars(DecideAbort(p))
  /\ \A p \in Proc: WF_vars(DecideCommit(p))

Spec == Init /\ [][Next]_vars /\ Fair

\* Failure detector completeness (temporal assumption)
\* If a process crashes and another never crashes, eventually the latter suspects the former.
FD_Completeness ==
  \A p \in Proc: \A q \in Proc:
    (<> (p \in Crashed) /\ [] (q \notin Crashed)) => <> (p \in Suspect[q])

\* Safety properties

Agreement ==
  [] ( \A p \in Proc: \A q \in Proc:
        (decision[p] # "Undecided" /\ decision[q] # "Undecided") => decision[p] = decision[q] )

AbortValidity ==
  [] ( SomeNo => (\A q \in Proc: decision[q] # "Commit") )

CommitOnlyIfAllYes ==
  [] ( \A q \in Proc: decision[q] = "Commit" => AllYes )

NoCommitIfCrash ==
  [] ( Crashed # {} => (\A q \in Proc: decision[q] # "Commit") )

CommitValidity == CommitOnlyIfAllYes /\ NoCommitIfCrash

\* Liveness properties

\* Termination for correct (never-crashing) processes
Termination ==
  \A p \in Proc: ( [] (p \notin Crashed) ) => <> (decision[p] # "Undecided")

\* Eventual commit under all-YES votes and no failures
NoFailure == [] (Crashed = {})
EventualCommit == (AllYes /\ NoFailure) => <> AllCommit

=============================================================================