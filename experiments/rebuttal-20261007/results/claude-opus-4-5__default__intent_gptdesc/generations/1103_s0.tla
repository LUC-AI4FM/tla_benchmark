---------------------------- MODULE NBAC ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, Proc

ASSUME N \in Nat /\ N > 0
ASSUME Proc = 1..N

VARIABLES
    vote,           \* vote[p] \in {YES, NO} - initial vote of process p
    crashed,        \* crashed[p] \in BOOLEAN - whether process p has crashed
    decision,       \* decision[p] \in {COMMIT, ABORT, UNDECIDED}
    sentVotes,      \* sentVotes[p] - set of processes to which p has sent its vote
    received,       \* received[p] - set of (sender, vote) pairs received by p
    suspected,      \* suspected[p][q] \in BOOLEAN - p's failure detector suspects q
    messages        \* messages - set of {src, dst, vote} records in transit

vars == <<vote, crashed, decision, sentVotes, received, suspected, messages>>

Votes == {"YES", "NO"}
Decisions == {"COMMIT", "ABORT", "UNDECIDED"}

TypeOK ==
    /\ vote \in [Proc -> Votes]
    /\ crashed \in [Proc -> BOOLEAN]
    /\ decision \in [Proc -> Decisions]
    /\ sentVotes \in [Proc -> SUBSET Proc]
    /\ received \in [Proc -> SUBSET (Proc \times Votes)]
    /\ suspected \in [Proc -> [Proc -> BOOLEAN]]
    /\ messages \subseteq [src: Proc, dst: Proc, vote: Votes]

Init ==
    /\ vote \in [Proc -> Votes]
    /\ crashed = [p \in Proc |-> FALSE]
    /\ decision = [p \in Proc |-> "UNDECIDED"]
    /\ sentVotes = [p \in Proc |-> {}]
    /\ received = [p \in Proc |-> {<<p, vote[p]>>}]
    /\ suspected = [p \in Proc |-> [q \in Proc |-> FALSE]]
    /\ messages = {}

SendVote(p, q) ==
    /\ ~crashed[p]
    /\ q \notin sentVotes[p]
    /\ sentVotes' = [sentVotes EXCEPT ![p] = @ \cup {q}]
    /\ messages' = messages \cup {[src |-> p, dst |-> q, vote |-> vote[p]]}
    /\ UNCHANGED <<vote, crashed, decision, received, suspected>>

ReceiveMessage(p, m) ==
    /\ ~crashed[p]
    /\ m \in messages
    /\ m.dst = p
    /\ received' = [received EXCEPT ![p] = @ \cup {<<m.src, m.vote>>}]
    /\ messages' = messages \ {m}
    /\ UNCHANGED <<vote, crashed, decision, sentVotes, suspected>>

Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVotes, received, suspected, messages>>

UpdateSuspicion(p, q, newSuspicion) ==
    /\ ~crashed[p]
    /\ suspected' = [suspected EXCEPT ![p][q] = newSuspicion]
    /\ UNCHANGED <<vote, crashed, decision, sentVotes, received, messages>>

ReceivedVotes(p) == {v : <<s, v>> \in received[p]}
ReceivedFrom(p) == {s : <<s, v>> \in received[p]}

AllVotesYes(p) == \A <<s, v>> \in received[p] : v = "YES"
SomeVoteNo(p) == \E <<s, v>> \in received[p] : v = "NO"

AllAccountedFor(p) ==
    \A q \in Proc : q \in ReceivedFrom(p) \/ suspected[p][q]

DecideCommit(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "UNDECIDED"
    /\ ReceivedFrom(p) = Proc
    /\ AllVotesYes(p)
    /\ \A q \in Proc : ~suspected[p][q]
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED <<vote, crashed, sentVotes, received, suspected, messages>>

DecideAbort(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "UNDECIDED"
    /\ \/ SomeVoteNo(p)
       \/ /\ AllAccountedFor(p)
          /\ \E q \in Proc : suspected[p][q] /\ q \notin ReceivedFrom(p)
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED <<vote, crashed, sentVotes, received, suspected, messages>>

Next ==
    \/ \E p, q \in Proc : SendVote(p, q)
    \/ \E p \in Proc : \E m \in messages : ReceiveMessage(p, m)
    \/ \E p \in Proc : Crash(p)
    \/ \E p, q \in Proc : \E b \in BOOLEAN : UpdateSuspicion(p, q, b)
    \/ \E p \in Proc : DecideCommit(p)
    \/ \E p \in Proc : DecideAbort(p)

Decided(p) == decision[p] \in {"COMMIT", "ABORT"}
Live(p) == ~crashed[p]

Agreement ==
    \A p, q \in Proc :
        (Live(p) /\ Live(q) /\ Decided(p) /\ Decided(q)) =>
            decision[p] = decision[q]

ValidityCommit ==
    \A p \in Proc :
        (Live(p) /\ decision[p] = "COMMIT") =>
            \A q \in Proc : vote[q] = "YES"

ValidityAbortNo ==
    \A p \in Proc :
        (\E q \in Proc : vote[q] = "NO") =>
            (Live(p) => decision[p] # "COMMIT")

Safety == Agreement /\ ValidityCommit /\ ValidityAbortNo

EventuallyAllVotesSent ==
    <>(\A p \in Proc : Live(p) => sentVotes[p] = Proc)

AccurateSuspicion(p) ==
    \A q \in Proc : (suspected[p][q] => crashed[q])

EventuallyAccurate ==
    <>(\A p \in Proc : Live(p) => AccurateSuspicion(p))

StrongCompleteness ==
    \A p \in Proc : crashed[p] =>
        <>(\A q \in Proc : Live(q) => suspected[q][p])

Termination ==
    \A p \in Proc : Live(p) => <>(Decided(p))

SendAction(p) == \E q \in Proc : SendVote(p, q)
ReceiveAction(p) == \E m \in messages : ReceiveMessage(p, m)
DecideAction(p) == DecideCommit(p) \/ DecideAbort(p)
SuspicionUpdate(p) == \E q \in Proc : \E b \in BOOLEAN : UpdateSuspicion(p, q, b)

Fairness ==
    /\ \A p \in Proc : WF_vars(SendAction(p))
    /\ \A p \in Proc : WF_vars(ReceiveAction(p))
    /\ \A p \in Proc : WF_vars(DecideAction(p))
    /\ \A p \in Proc : WF_vars(SuspicionUpdate(p))

Spec == Init /\ [][Next]_vars /\ Fairness

TerminationUnderAccuracy ==
    (EventuallyAccurate /\ StrongCompleteness) => Termination

THEOREM Spec => []Safety

THEOREM Spec => TerminationUnderAccuracy

========================================================================