------------------------------ MODULE NBAC ------------------------------
EXTENDS Naturals, Sequences, Temporal

CONSTANT N

VARIABLES vote, crashed, sentVote, receivedVotes, decisions, suspectedSet

(* Set of processes *)
Proc == 1..N

(* Type invariant *)
TypeOK ==
  /\ vote \in [Proc -> {"YES","NO"}]
  /\ crashed \in [Proc -> BOOLEAN]
  /\ sentVote \in [Proc -> BOOLEAN]
  /\ receivedVotes \in [Proc -> SUBSET Proc]
  /\ decisions \in [Proc -> {"COMMIT","ABORT","UNDECIDED"}]
  /\ suspectedSet \subseteq Proc

(* Initial state *)
Init ==
  /\ crashed = [p \in Proc |-> FALSE]
  /\ sentVote = [p \in Proc |-> FALSE]
  /\ receivedVotes = [p \in Proc |-> {}]
  /\ decisions = [p \in Proc |-> "UNDECIDED"]
  /\ suspectedSet = {}
  /\ vote \in [Proc -> {"YES","NO"}]   (* arbitrary votes *)

(* Actions *)
SendVote(p) ==
  /\ ~crashed[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, crashed, receivedVotes, decisions, suspectedSet>>

ReceiveVote(p,q) ==
  /\ ~crashed[p]
  /\ ~crashed[q]
  /\ sentVote[q]
  /\ q \in Proc
  /\ q /= p
  /\ q \notin receivedVotes[p]
  /\ receivedVotes' = [receivedVotes EXCEPT ![p] = receivedVotes[p] \cup {q}]
  /\ UNCHANGED <<vote, crashed, sentVote, decisions, suspectedSet>>

Crash(p) ==
  /\ ~crashed[p]
  /\ crashed' = [crashed EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, sentVote, receivedVotes, decisions, suspectedSet>>

UpdateSuspected(S') ==
  /\ S' \subseteq Proc
  /\ suspectedSet' = S'
  /\ UNCHANGED <<vote, crashed, sentVote, receivedVotes, decisions>>

AbortDecision(p) ==
  /\ ~crashed[p]
  /\ decisions[p] = "UNDECIDED"
  /\ ( (\E q \in suspectedSet : TRUE)
       \/ (\E q \in receivedVotes[p] : vote[q]="NO") )
  /\ decisions' = [decisions EXCEPT ![p] = "ABORT"]
  /\ UNCHANGED <<vote, crashed, sentVote, receivedVotes, suspectedSet>>

CommitDecision(p) ==
  /\ ~crashed[p]
  /\ decisions[p] = "UNDECIDED"
  /\ sentVote[p]
  /\ receivedVotes[p] = Proc
  /\ (\A q \in Proc : vote[q]="YES")
  /\ suspectedSet = {}
  /\ decisions' = [decisions EXCEPT ![p] = "COMMIT"]
  /\ UNCHANGED <<vote, crashed, sentVote, receivedVotes, suspectedSet>>

Next ==
  \E p \in Proc : SendVote(p)
  \/ \E p,q \in Proc : (p /= q) /\ ReceiveVote(p,q)
  \/ \E p \in Proc : Crash(p)
  \/ \E S' \subseteq Proc : UpdateSuspected(S')
  \/ \E p \in Proc : AbortDecision(p)
  \/ \E p \in Proc : CommitDecision(p)

NonCrashActions ==
  \E p \in Proc : SendVote(p)
  \/ \E p,q \in Proc : (p /= q) /\ ReceiveVote(p,q)
  \/ \E S' \subseteq Proc : UpdateSuspected(S')
  \/ \E p \in Proc : AbortDecision(p)
  \/ \E p \in Proc : CommitDecision(p)

Spec ==
  Init
  /\ [][Next]_<<vote, crashed, sentVote, receivedVotes, decisions, suspectedSet>>
  /\ WF_vars(NonCrashActions)

(* LTL properties *)
AgrrLtl ==
  [] (\A p,q \in Proc :
        ~crashed[p] /\ ~crashed[q]
        => (decisions[p]="UNDECIDED" \/ decisions[q]="UNDECIDED" \/ decisions[p]=decisions[q]))

AbortValidityLtl ==
  [] ((\E p \in Proc : vote[p]="NO") => [] (\A p \in Proc : decisions[p] /= "COMMIT"))

CommitValidityLtl ==
  [] (((\A p \in Proc : vote[p]="YES") /\ suspectedSet = {}) => [] (\A p \in Proc : decisions[p] /= "ABORT"))

TerminationLtl ==
  [] ((~(\E p \in Proc : crashed[p]) /\ suspectedSet = {})
      => <> (\A p \in Proc : decisions[p] /= "UNDECIDED"))

============================================================================