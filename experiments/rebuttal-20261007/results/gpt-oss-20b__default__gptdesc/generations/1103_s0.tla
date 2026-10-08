MODULE NBAC
EXTENDS Naturals, Sequences, TLC

CONSTANT N

VARIABLES vote, decision, inbox, fdSuspects, crashed, sentVote, receivedVotes

ProcSet == 1..N

Message == [type: {"VOTE","DECISION"}, from: ProcSet, content: {"YES","NO","COMMIT","ABORT"}]

vars == <<vote, decision, inbox, fdSuspects, crashed, sentVote, receivedVotes>>

Init ==
    /\ vote \in [ProcSet -> {"YES","NO"}]
    /\ decision = [p \in ProcSet |-> "UNDECIDED"]
    /\ inbox = [p \in ProcSet |-> {}]
    /\ fdSuspects = [p \in ProcSet |-> {}]
    /\ crashed = [p \in ProcSet |-> FALSE]
    /\ sentVote = [p \in ProcSet |-> FALSE]
    /\ receivedVotes = [p \in ProcSet |-> {}]

SendVote(p) ==
    /\ ¬crashed[p]
    /\ ¬sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ inbox' = [q \in ProcSet |
                    IF q = p THEN inbox[q]
                    ELSE inbox[q] ∪ {<"VOTE", p, vote[p]>}]
    /\ UNCHANGED <<vote, decision, fdSuspects, crashed, receivedVotes>>

ReceiveMsg(p) ==
    /\ ¬crashed[p]
    /\ inbox[p] ≠ {}
    /\ m \in inbox[p]
    /\ inbox' = [q \in ProcSet |
                    IF q = p THEN inbox[q] \ {m}
                    ELSE inbox[q]]
    /\ IF m.type = "VOTE" THEN
           receivedVotes' = [r \in ProcSet |
                               IF r = p THEN receivedVotes[r] ∪ {[from: m.from, vote: m.content]}
                               ELSE receivedVotes[r]]
       ELSE
           decision' = [r \in ProcSet |
                           IF r = p /\ decision[p]="UNDECIDED" THEN m.content
                           ELSE decision[r]]
    /\ UNCHANGED <<vote, sentVote, fdSuspects, crashed>>

AddSuspect(p,q) ==
    /\ ¬crashed[p]
    /\ q ∈ ProcSet \ {p}
    /\ fdSuspects' = [r \in ProcSet |
                        IF r = p THEN fdSuspects[r] ∪ {q}
                        ELSE fdSuspects[r]]
    /\ UNCHANGED <<vote, decision, inbox, crashed, sentVote, receivedVotes>>

RemoveSuspect(p,q) ==
    /\ ¬crashed[p]
    /\ q ∈ ProcSet \ {p}
    /\ fdSuspects' = [r \in ProcSet |
                        IF r = p THEN fdSuspects[r] \ {q}
                        ELSE fdSuspects[r]]
    /\ UNCHANGED <<vote, decision, inbox, crashed, sentVote, receivedVotes>>

Crash(p) ==
    /\ ¬crashed[p]
    /\ crashed' = [r \in ProcSet |
                    IF r = p THEN TRUE
                    ELSE crashed[r]]
    /\ UNCHANGED <<vote, decision, inbox, fdSuspects, sentVote, receivedVotes>>

Decide(p) ==
    /\ ¬crashed[p]
    /\ decision[p] = "UNDECIDED"
    /\ LET nonSuspected == ProcSet \ fdSuspects[p] IN
       /\ ∀q ∈ nonSuspected : ∃v ∈ {"YES","NO"} : [from: q, vote: v] ∈ receivedVotes[p]
       /\ decision' = [r \in ProcSet |
                         IF r = p THEN
                            IF ∀q ∈ nonSuspected : [from: q, vote: "YES"] ∈ receivedVotes[p]
                            THEN "COMMIT"
                            ELSE "ABORT"
                         ELSE decision[r]]
    /\ UNCHANGED <<vote, inbox, fdSuspects, crashed, sentVote, receivedVotes>>

Next ==
    ∃p ∈ ProcSet :
        (SendVote(p)
         \/ ReceiveMsg(p)
         \/ ∃q ∈ ProcSet \ {p} : AddSuspect(p,q)
         \/ ∃q ∈ ProcSet \ {p} : RemoveSuspect(p,q)
         \/ Crash(p)
         \/ Decide(p))

TypeInv ==
    /\ vote \in [ProcSet -> {"YES","NO"}]
    /\ decision \in [ProcSet -> {"UNDECIDED", "COMMIT", "ABORT"}]
    /\ inbox \in [ProcSet -> SUBSET Message]
    /\ fdSuspects \in [ProcSet -> SUBSET ProcSet]
    /\ crashed \in [ProcSet -> BOOLEAN]
    /\ sentVote \in [ProcSet -> BOOLEAN]
    /\ receivedVotes \in [ProcSet -> SUBSET [from: ProcSet, vote: {"YES","NO"}]]
    /\ ∀p ∈ ProcSet : decision[p] = "UNDECIDED" \/ decision[p] = "COMMIT" \/ decision[p] = "ABORT"
    /\ ∀p ∈ ProcSet : ∀m \in inbox[p] :
          m.type ∈ {"VOTE","DECISION"} /\ m.from ∈ ProcSet
          /\ m.content ∈ {"YES","NO","COMMIT","ABORT"}

ValidUnanimous ==
    ∀p ∈ ProcSet : vote[p] = "YES" => ◇ (∃q ∈ ProcSet : decision[q] = "COMMIT")

Spec == Init /\ [][Next]_vars

THEOREM Safety == Spec => []TypeInv
THEOREM Liveness == Spec => ValidUnanimous

END MODULE