---------------------------- MODULE NBAC ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Proc     == 1..N
Votes    == {"Yes", "No"}
Values   == {"Commit", "Abort"}
None     == "None"

VARIABLES
    pc,          \* local control state of each process
    vote,        \* vote cast by each process
    sent,        \* broadcast vote messages: set of <<sender, vote>>
    rcvdYes,     \* rcvdYes[i]: senders from whom i received a Yes vote
    rcvdNo,      \* rcvdNo[i]: senders from whom i received a No vote
    crashed,     \* set of crashed processes
    suspected,   \* suspected[i]: TRUE iff i's failure detector reported a failure
    proposal,    \* value each process proposed to the consensus layer
    consensus,   \* value decided by the (abstract) consensus layer
    decision     \* final decision of each process

vars == << pc, vote, sent, rcvdYes, rcvdNo, crashed, suspected,
           proposal, consensus, decision >>

Alive == Proc \ crashed

NumYes(i) == Cardinality(rcvdYes[i])
NumNo(i)  == Cardinality(rcvdNo[i])

TypeOK ==
    /\ pc        \in [Proc -> {"init", "voted", "proposed", "decided"}]
    /\ vote      \in [Proc -> Votes \cup {None}]
    /\ sent      \subseteq (Proc \X Votes)
    /\ rcvdYes   \in [Proc -> SUBSET Proc]
    /\ rcvdNo    \in [Proc -> SUBSET Proc]
    /\ crashed   \subseteq Proc
    /\ suspected \in [Proc -> BOOLEAN]
    /\ proposal  \in [Proc -> Values \cup {None}]
    /\ consensus \in Values \cup {None}
    /\ decision  \in [Proc -> Values \cup {None}]

Init ==
    /\ pc        = [i \in Proc |-> "init"]
    /\ vote      = [i \in Proc |-> None]
    /\ sent      = {}
    /\ rcvdYes   = [i \in Proc |-> {}]
    /\ rcvdNo    = [i \in Proc |-> {}]
    /\ crashed   = {}
    /\ suspected = [i \in Proc |-> FALSE]
    /\ proposal  = [i \in Proc |-> None]
    /\ consensus = None
    /\ decision  = [i \in Proc |-> None]

\* Voting phase: a process casts its vote and broadcasts it.
Vote(i, v) ==
    /\ i \in Alive
    /\ pc[i] = "init"
    /\ vote' = [vote EXCEPT ![i] = v]
    /\ sent' = sent \cup {<<i, v>>}
    /\ pc'   = [pc EXCEPT ![i] = "voted"]
    /\ UNCHANGED << rcvdYes, rcvdNo, crashed, suspected,
                    proposal, consensus, decision >>

\* Message reception: process i receives the vote of process j.
Receive(i, j) ==
    /\ i \in Alive
    /\ pc[i] = "voted"
    /\ j \notin rcvdYes[i] \cup rcvdNo[i]
    /\ \E v \in Votes :
         /\ <<j, v>> \in sent
         /\ IF v = "Yes"
              THEN /\ rcvdYes' = [rcvdYes EXCEPT ![i] = @ \cup {j}]
                   /\ UNCHANGED rcvdNo
              ELSE /\ rcvdNo' = [rcvdNo EXCEPT ![i] = @ \cup {j}]
                   /\ UNCHANGED rcvdYes
    /\ UNCHANGED << pc, vote, sent, crashed, suspected,
                    proposal, consensus, decision >>

\* A process may crash at any time.
Crash(i) ==
    /\ i \in Alive
    /\ crashed' = crashed \cup {i}
    /\ UNCHANGED << pc, vote, sent, rcvdYes, rcvdNo, suspected,
                    proposal, consensus, decision >>

\* Failure detector (accurate & complete): only reports real crashes.
Detect(i) ==
    /\ i \in Alive
    /\ crashed # {}
    /\ ~suspected[i]
    /\ suspected' = [suspected EXCEPT ![i] = TRUE]
    /\ UNCHANGED << pc, vote, sent, rcvdYes, rcvdNo, crashed,
                    proposal, consensus, decision >>

\* Proposal: once enough information is available, propose Commit iff
\* all N Yes votes were received and no failure was detected.
Propose(i) ==
    /\ i \in Alive
    /\ pc[i] = "voted"
    /\ \/ NumYes(i) = N
       \/ NumNo(i) > 0
       \/ suspected[i]
    /\ LET p == IF NumYes(i) = N /\ NumNo(i) = 0 /\ ~suspected[i]
                  THEN "Commit" ELSE "Abort"
       IN /\ proposal'  = [proposal EXCEPT ![i] = p]
          /\ consensus' = IF consensus = None THEN p ELSE consensus
    /\ pc' = [pc EXCEPT ![i] = "proposed"]
    /\ UNCHANGED << vote, sent, rcvdYes, rcvdNo, crashed, suspected, decision >>

\* Decision: adopt the value decided by the consensus layer (once).
Decide(i) ==
    /\ i \in Alive
    /\ pc[i] = "proposed"
    /\ consensus # None
    /\ decision' = [decision EXCEPT ![i] = consensus]
    /\ pc'       = [pc EXCEPT ![i] = "decided"]
    /\ UNCHANGED << vote, sent, rcvdYes, rcvdNo, crashed, suspected,
                    proposal, consensus >>

Next ==
    \/ \E i \in Proc, v \in Votes : Vote(i, v)
    \/ \E i, j \in Proc : Receive(i, j)
    \/ \E i \in Proc : Crash(i)
    \/ \E i \in Proc : Detect(i)
    \/ \E i \in Proc : Propose(i)
    \/ \E i \in Proc : Decide(i)
    \/ (\A i \in Proc : pc[i] = "decided" \/ i \in crashed) /\ UNCHANGED vars

Fairness ==
    /\ \A i \in Proc : WF_vars(\E v \in Votes : Vote(i, v))
    /\ \A i, j \in Proc : WF_vars(Receive(i, j))
    /\ \A i \in Proc : WF_vars(Detect(i))
    /\ \A i \in Proc : WF_vars(Propose(i))
    /\ \A i \in Proc : WF_vars(Decide(i))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------
\* Correctness properties

Agreement ==
    \A i, j \in Proc :
        (decision[i] # None /\ decision[j] # None) => decision[i] = decision[j]

CommitValidity ==
    (\E i \in Proc : decision[i] = "Commit") =>
        /\ \A j \in Proc : vote[j] = "Yes"
        /\ \E j \in Proc : proposal[j] = "Commit"

AbortValidity ==
    ((\E j \in Proc : vote[j] = "No") /\ (\E i \in Proc : decision[i] # None))
        => \A i \in Proc : decision[i] # "Commit"

Integrity ==
    [][\A i \in Proc : decision[i] # None => decision'[i] = decision[i]]_vars

Termination ==
    <>(\A i \in Proc : i \in crashed \/ decision[i] # None)

=====================================================================