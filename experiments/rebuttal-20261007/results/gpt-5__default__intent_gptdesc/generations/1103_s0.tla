------------------------------ MODULE AtomicCommitFD ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANT Proc

(*
  Values
*)
VoteVals == {"YES", "NO"}
DecisionVals == {"Undecided", "Commit", "Abort"}

(*
  Messages are records carrying a vote from -> to with a value in VoteVals.
*)
Msg == [from: Proc, to: Proc, val: VoteVals]

VARIABLES
  vote,       \* vote \in [Proc -> VoteVals], fixed after Init
  Crashed,    \* Crashed \subseteq Proc, grows monotonically
  Suspect,    \* Suspect \in [Proc -> [Proc -> BOOLEAN]], unreliable FD, can change arbitrarily
  recv,       \* recv \in [Proc -> [Proc -> [ "YES", "NO", "None" ]]]
  sent,       \* sent \in [Proc -> [Proc -> BOOLEAN]], whether p has sent its vote to q (for fairness)
  chan,       \* chan \subseteq Msg, set of in-flight messages
  decided     \* decided \in [Proc -> DecisionVals]

Vars == << vote, Crashed, Suspect, recv, sent, chan, decided >>

(*
  Type correctness
*)
TypeOK ==
  /\ vote \in [Proc -> VoteVals]
  /\ Crashed \subseteq Proc
  /\ Suspect \in [Proc -> [Proc -> BOOLEAN]]
  /\ recv \in [Proc -> [Proc -> {"YES", "NO", "None"}]]
  /\ sent \in [Proc -> [Proc -> BOOLEAN]]
  /\ chan \subseteq Msg
  /\ decided \in [Proc -> DecisionVals]

(*
  Initialization:
  - Arbitrary initial votes
  - No messages in-flight
  - Each process knows its own vote
  - No decisions taken
  - sent flags false
  - Failure detector arbitrary
  - Crashed arbitrary subset (can model initial crashes)
*)
Init ==
  /\ vote \in [Proc -> VoteVals]
  /\ Crashed \subseteq Proc
  /\ Suspect \in [Proc -> [Proc -> BOOLEAN]]
  /\ recv = [p \in Proc |-> [q \in Proc |-> IF q = p THEN vote[p] ELSE "None"]]
  /\ sent = [p \in Proc |-> [q \in Proc |-> FALSE]]
  /\ chan = {}
  /\ decided = [p \in Proc |-> "Undecided"]
  /\ TypeOK

(*
  Helper to build a message from p to q carrying p's vote
*)
Message(p, q) == [from |-> p, to |-> q, val |-> vote[p]]

(*
  Actions
*)

Send(p, q) ==
  /\ p \in Proc /\ q \in Proc /\ p # q
  /\ p \notin Crashed
  /\ ~sent[p][q]
  /\ chan' = chan \cup { Message(p, q) }
  /\ sent' = [sent EXCEPT ![p][q] = TRUE]
  /\ UNCHANGED << vote, Crashed, Suspect, recv, decided >>

Deliver(m) ==
  /\ m \in chan
  /\ LET r == m.to IN
     /\ chan' = chan \ { m }
     /\ recv' = IF r \in Crashed THEN recv
                ELSE [recv EXCEPT ![r][m.from] = m.val]
     /\ UNCHANGED << vote, Crashed, Suspect, sent, decided >>

CrashAct(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ Crashed' = Crashed \cup { p }
  /\ UNCHANGED << vote, Suspect, recv, sent, chan, decided >>

FDStep ==
  /\ \E S \in [Proc -> [Proc -> BOOLEAN]] : Suspect' = S
  /\ UNCHANGED << vote, Crashed, recv, sent, chan, decided >>

DecideCommit(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ decided[p] = "Undecided"
  /\ \A q \in Proc : recv[p][q] = "YES"
  /\ decided' = [decided EXCEPT ![p] = "Commit"]
  /\ UNCHANGED << vote, Crashed, Suspect, recv, sent, chan >>

DecideAbort(p) ==
  /\ p \in Proc
  /\ p \notin Crashed
  /\ decided[p] = "Undecided"
  /\ ( \E q \in Proc : recv[p][q] = "NO")
     \/ ( \E q \in Proc : (recv[p][q] = "None") /\ Suspect[p][q] )
  /\ decided' = [decided EXCEPT ![p] = "Abort"]
  /\ UNCHANGED << vote, Crashed, Suspect, recv, sent, chan >>

SendAny == \E p \in Proc : \E q \in Proc \ {p} : Send(p, q)
DeliverAny == \E m \in Msg : Deliver(m)
CrashAny == \E p \in Proc \ Crashed : CrashAct(p)
DecideCommitAny == \E p \in Proc : DecideCommit(p)
DecideAbortAny == \E p \in Proc : DecideAbort(p)

Next ==
  SendAny
  \/ DeliverAny
  \/ CrashAny
  \/ FDStep
  \/ DecideCommitAny
  \/ DecideAbortAny

(*
  Fairness assumptions (weak fairness):
  - If a non-crashed process continuously has not yet sent to a peer, it eventually sends.
  - If a specific message remains in the channel, it is eventually delivered.
  - If a decision (commit/abort) for a process remains continuously enabled, it eventually happens.
*)
FairSend ==
  \A p \in Proc : \A q \in Proc :
    (p # q) => WF_Vars(Send(p, q))

FairDeliver ==
  \A m \in Msg : WF_Vars(Deliver(m))

FairDecide ==
  \A p \in Proc : WF_Vars(DecideCommit(p)) /\ WF_Vars(DecideAbort(p))

Spec == Init /\ [][Next]_Vars /\ FairSend /\ FairDeliver /\ FairDecide

(*
  Safety invariants
*)

AgreementInv ==
  \A p \in Proc : \A q \in Proc :
    ~( (p \notin Crashed) /\ (q \notin Crashed)
       /\ decided[p] = "Commit" /\ decided[q] = "Abort" )

ValidityInv ==
  ( \E q \in Proc : vote[q] = "NO" )
  => ( \A p \in Proc : (p \in Crashed) \/ decided[p] # "Commit" )

(*
  Liveness assumptions and properties
*)

Decided(p) == decided[p] # "Undecided"

(*
  Eventual accuracy/stabilization of the failure detector after the last crash:
  - Eventually, the set of crashed processes stops changing.
  - Eventually, all crashed are suspected by everyone.
  - Eventually, no correct (non-crashed) process is suspected by anyone.
*)
EventualAccuracy ==
  /\ <>[] (UNCHANGED Crashed)
  /\ <>[] ( \A p \in Proc : \A q \in Proc : (q \in Crashed) => Suspect[p][q] )
  /\ <>[] ( \A p \in Proc : \A q \in Proc : (q \notin Crashed) => ~Suspect[p][q] )

(*
  Non-blocking termination under eventual accuracy:
  Every non-crashed process eventually decides (commit or abort).
*)
TerminationUnderEA ==
  EventualAccuracy => (\A p \in Proc : [] (p \notin Crashed => <> Decided(p)))

(*
  Validity (commit possibility) under all-YES and no failures:
  If all processes voted YES and no crashes ever occur, then eventually all non-crashed
  processes decide Commit (given fairness and eventual accuracy of suspicions).
*)
AllYes == \A p \in Proc : vote[p] = "YES"

NoFailures == [] (Crashed = {})

CommitUnderAllYesNoFailures ==
  (AllYes /\ NoFailures /\ EventualAccuracy)
  => (\A p \in Proc : [] (p \notin Crashed => <> (decided[p] = "Commit")))

=============================================================================