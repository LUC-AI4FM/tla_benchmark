------------------------------- MODULE NBACProtocol -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N \* Number of processes

VARIABLES pc, sent, rcvd, fd

Init == 
  /\ pc = [p \in 1..N -> CHOOSE v \in {"YES", "NO"}]
  /\ sent = {}
  /\ rcvd = [p \in 1..N -> {}]
  /\ fd = FALSE

InitAllYes ==
  /\ pc = [p \in 1..N -> "YES"]
  /\ sent = {}
  /\ rcvd = [p \in 1..N -> {}]
  /\ fd = FALSE

UponYes(p) == 
  /\ pc[p] = "YES"
  /\ fd = FALSE
  /\ pc' = [pc EXCEPT ![p] = "SENT"]
  /\ sent' = sent \cup {<<p, "YES">>}
  /\ rcvd' = rcvd
  /\ fd' = fd

UponNo(p) == 
  /\ pc[p] = "NO"
  /\ fd = FALSE
  /\ pc' = [pc EXCEPT ![p] = "SENT"]
  /\ sent' = sent \cup {<<p, "NO">>}
  /\ rcvd' = rcvd
  /\ fd' = fd

UponSent(p) == 
  /\ pc[p] = "SENT"
  /\ LET yesCount == Cardinality({msg \in sent : msg[2] = "YES"})
     IN IF fd \/ yesCount < N
        THEN pc' = [pc EXCEPT ![p] = "ABORT"]
        ELSE pc' = [pc EXCEPT ![p] = "COMMIT"]
  /\ sent' = sent
  /\ rcvd' = rcvd
  /\ fd' = fd

UponCrash(p) == 
  /\ pc[p] \in {"YES", "NO", "SENT"}
  /\ pc' = [pc EXCEPT ![p] = "CRASH"]
  /\ sent' = sent
  /\ rcvd' = rcvd
  /\ fd' = TRUE

Next ==
  \/ \E p \in 1..N : UponYes(p)
  \/ \E p \in 1..N : UponNo(p)
  \/ \E p \in 1..N : UponSent(p)
  \/ \E p \in 1..N : UponCrash(p)

Spec ==
  /\ Init
  /\ [][Next]_<<pc, sent, rcvd, fd>>
  /\ WF_next(<<pc, sent, rcvd, fd>>)

TypeOK ==
  /\ pc \in [1..N -> {"YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH"}]
  /\ sent \subseteq (1..N) \X {"YES", "NO"}
  /\ rcvd \in [1..N -> SUBSET (1..N) \X {"YES", "NO"}]
  /\ fd \in BOOLEAN

Validity ==
  \/ \A p \in 1..N : pc[p] = "COMMIT" => (\A q \in 1..N : pc[q] = "YES")
  \/ \E p \in 1..N : pc[p] = "ABORT"

=============================================================================