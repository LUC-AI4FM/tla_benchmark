MODULE NBAC
EXTENDS Naturals, Sequences, TLC

CONSTANTS ProcSet \* Set of processes

(* ------------------------------------------------------------------ *)
(* Types and constants *)

SUBSET VoteVal = {"YES","NO","UNDECIDED","NONE"}
SUBSET DecisionVal = {"COMMIT","ABORT","PENDING"}
SUBSET StatusVal = {"alive","crashed"}
SUBSET MsgType = {"VOTE","DECISION"}

Message == [ type : MsgType, from : ProcSet, val : VoteVal \/ DecisionVal ]

AllMsgs == { m \in [type : MsgType, from : ProcSet, val : VoteVal \/ DecisionVal] }

(* ------------------------------------------------------------------ *)
(* Variables *)

VARIABLES status, vote, decision, inbox, fd, receivedVotes

vars == <<status, vote, decision, inbox, fd, receivedVotes>>

(* ------------------------------------------------------------------ *)
(* Initial state *)

Init ==
    /\ status ∈ [ProcSet -> StatusVal]
    /\ vote   ∈ [ProcSet -> {"YES","NO","UNDECIDED"}]
    /\ decision = "PENDING"
    /\ inbox  ∈ [ProcSet -> SUBSET AllMsgs]
    /\ fd     ∈ [ProcSet -> SUBSET ProcSet]
    /\ receivedVotes ∈ [ProcSet -> [ProcSet -> VoteVal]]
    /\ \A p ∈ ProcSet: status[p] = "alive"
    /\ \A p ∈ ProcSet: vote[p] = "UNDECIDED"
    /\ inbox = [p ∊ ProcSet |-> {}]
    /\ fd     = [p ∊ ProcSet |-> {}]
    /\ receivedVotes = [p ∊ ProcSet |-> [q ∊ ProcSet |-> "NONE"]]

(* ------------------------------------------------------------------ *)
(* Actions *)

Vote(p) ==
    /\ p ∈ ProcSet
    /\ status[p] = "alive"
    /\ vote[p] = "UNDECIDED"
    /\ vote'   = [vote EXCEPT ![p] = CHOOSE v \in {"YES","NO"} : TRUE]
    /\ UNCHANGED <<status, decision, inbox, fd, receivedVotes>>

SendVote(p) ==
    /\ p ∈ ProcSet
    /\ status[p] = "alive"
    /\ vote[p] ∈ {"YES","NO"}
    /\ inbox' = [q ∊ ProcSet |
                    IF q /= p THEN inbox[q] \cup { [type |-> "VOTE", from |-> p, val |-> vote[p]] }
                    ELSE inbox[q]]
    /\ UNCHANGED <<status, vote, decision, fd, receivedVotes>>

ReceiveVote ==
    LET r == CHOOSE r1 ∈ ProcSet : status[r1] = "alive" /\ inbox[r1] ≠ {}
        m == CHOOSE m1 ∈ inbox[r] : TRUE
    IN  /\ inbox' = [q ∊ ProcSet |
                        IF q = r THEN inbox[q] \ {m}
                        ELSE inbox[q]]
        /\ receivedVotes' =
               [p ∊ ProcSet |
                    IF p = r THEN [q ∊ ProcSet | IF q = m.from THEN m.val ELSE receivedVotes[p][q]]
                    ELSE receivedVotes[p]]
        /\ UNCHANGED <<status, vote, decision, fd>>

Decide ==
    LET p == CHOOSE p1 ∈ ProcSet : status[p1] = "alive"
    IN  /\ decision = "PENDING"
        /\ \A q ∈ ProcSet : status[q] = "alive" => receivedVotes[p][q] ≠ "NONE"
        /\ IF \A q ∈ ProcSet : status[q] = "alive" /\ receivedVotes[p][q] = "YES"
           THEN decision' = "COMMIT"
           ELSE decision' = "ABORT"
        /\ inbox' = [q ∊ ProcSet |
                        IF status[q]="alive" THEN inbox[q] \cup { [type |-> "DECISION", from |-> p, val |-> decision'] }
                        ELSE inbox[q]]
        /\ UNCHANGED <<status, vote, fd, receivedVotes>>

ReceiveDecision ==
    LET r == CHOOSE r1 ∈ ProcSet : status[r1] = "alive" /\ inbox[r1] ≠ {}
        m == CHOOSE m1 ∈ inbox[r] : m.type = "DECISION"
    IN  /\ inbox' = [q ∊ ProcSet |
                        IF q = r THEN inbox[q] \ {m}
                        ELSE inbox[q]]
        /\ decision' = m.val
        /\ UNCHANGED <<status, vote, fd, receivedVotes>>

FDUpdate(p) ==
    /\ p ∈ ProcSet
    /\ status[p] = "alive"
    /\ fd' = [fd EXCEPT ![p] = CHOOSE s \in SUBSET ProcSet : TRUE]
    /\ UNCHANGED <<status, vote, decision, inbox, receivedVotes>>

Crash(p) ==
    /\ p ∈ ProcSet
    /\ status[p] = "alive"
    /\ status' = [status EXCEPT ![p] = "crashed"]
    /\ inbox'  = [q ∊ ProcSet | IF q = p THEN {} ELSE inbox[q]]
    /\ fd'     = [fd EXCEPT ![p] = {}]
    /\ UNCHANGED <<vote, decision, receivedVotes>>

Next ==
    \/ \E p ∈ ProcSet : Vote(p)
    \/ \E p ∈ ProcSet : SendVote(p)
    \/ ReceiveVote
    \/ Decide
    \/ ReceiveDecision
    \/ \E p ∈ ProcSet : FDUpdate(p)
    \/ \E p ∈ ProcSet : Crash(p)

(* ------------------------------------------------------------------ *)
(* Type invariants *)

TypeInv ==
    /\ status ∈ [ProcSet -> StatusVal]
    /\ vote   ∈ [ProcSet -> {"YES","NO","UNDECIDED"}]
    /\ decision ∈ DecisionVal
    /\ inbox  ∈ [ProcSet -> SUBSET AllMsgs]
    /\ fd     ∈ [ProcSet -> SUBSET ProcSet]
    /\ receivedVotes ∈ [ProcSet -> [ProcSet -> VoteVal]]

(* ------------------------------------------------------------------ *)
(* Validity invariant *)

ValidityInv ==
    decision = "COMMIT" => \A p ∈ ProcSet : vote[p] = "YES"

(* ------------------------------------------------------------------ *)
(* Spec *)

Spec == Init /\ [][Next]_vars /\ TypeInv /\ ValidityInv

============================================================================