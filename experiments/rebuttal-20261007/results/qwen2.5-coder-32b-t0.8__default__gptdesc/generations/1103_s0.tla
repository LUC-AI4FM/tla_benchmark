---------------------------- MODULE NBAC ----------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS N          \* Number of processes
ASSUME N > 0

VARIABLES 
    vote,           \* vote[p] is the vote (YES or NO) of process p
    msgSent,        \* msgSent[p][q] is a sequence of messages sent by p to q
    msgRecvd,       \* msgRecvd[p] is a set of messages received by p
    crashed,        \* crashed[p] indicates if process p has crashed
    localFD         \* localFD[p] is the failure detector view of p

Init == 
    /\ FORALL p \in 1..N: vote[p] = "UNKNOWN"
    /\ FORALL p \in 1..N, q \in 1..N: msgSent[p][q] = << >>
    /\ FORALL p \in 1..N: msgRecvd[p] = {}
    /\ FORALL p \in 1..N: crashed[p] = FALSE
    /\ FORALL p \in 1..N: localFD[p] = {}

Next == 
    \/ EXIST p \in 1..N, q \in 1..N, m \in {"YES", "NO"}:
        \* Process p sends a message to process q
        /\ crashed[p] = FALSE
        /\ LET newMsgSent == [msgSent EXCEPT ![p][q] = Append(msgSent[p][q], m)] 
        IN \/ /\ newMsgSent = msgSent'
           /\ msgRecvd' = [msgRecvd EXCEPT ![q] = msgRecvd[q] \cup {m}]
           /\ UNCHANGED <<vote, crashed, localFD>>
    \/ EXIST p \in 1..N:
        \* Process p updates its vote
        /\ crashed[p] = FALSE
        /\ LET newVote == CHOOSE v \in {"YES", "NO"}: TRUE 
        IN \/ /\ vote' = [vote EXCEPT ![p] = newVote]
           /\ UNCHANGED <<msgSent, msgRecvd, crashed, localFD>>
    \/ EXIST p \in 1..N:
        \* Process p updates its failure detector view
        /\ LET newLocalFD == CHOOSE fd \in [1..N -> BOOLEAN]: TRUE 
        IN \/ /\ localFD' = [localFD EXCEPT ![p] = newLocalFD]
           /\ UNCHANGED <<vote, msgSent, msgRecvd, crashed>>
    \/ EXIST p \in 1..N:
        \* Process p crashes
        /\ LET newCrashed == [crashed EXCEPT ![p] = TRUE] 
        IN \/ /\ crashed' = newCrashed
           /\ UNCHANGED <<vote, msgSent, msgRecvd, localFD>>

Spec ==
    Init /\ [][Next]_<<vote, msgSent, msgRecvd, crashed, localFD>> 

TypeInvariant == 
    /\ FORALL p \in 1..N: vote[p] \in {"YES", "NO", "UNKNOWN"}
    /\ FORALL p \in 1..N, q \in 1..N: msgSent[p][q] \in Seq({"YES", "NO"})
    /\ FORALL p \in 1..N: msgRecvd[p] \subseteq {"YES", "NO"}
    /\ FORALL p \in 1..N: crashed[p] \in BOOLEAN
    /\ FORALL p \in 1..N: localFD[p] \in [1..N -> BOOLEAN]

Validity ==
    \/ ~(\E v \in {"YES", "NO"}: FORALL p \in 1..N: vote[p] = v)
    \/ (FORALL p \in 1..N: vote[p] = "YES")

Invariant == TypeInvariant /\ Validity

WF == 
    WF_vars(<<vote, msgSent, msgRecvd, crashed, localFD>>, _)

Liveness ==
    [](TypeInvariant) -> <>(Validity)

THEOREM Spec => []Invariant
THEOREM Spec => WF /\ Liveness

====================================================================