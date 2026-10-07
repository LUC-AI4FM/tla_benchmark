```tla
MODULE NBAC
EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLES pc, sent, rcvd, fd

Init == 
  /\ pc = [i \in 1..N |-> IF i = 1 THEN "YES" ELSE "NO"]
  /\ sent = {}
  /\ rcvd = [i \in 1..N |-> {}]
  /\ fd = [i \in 1..N |-> FALSE]

InitAllYes == 
  /\ pc = [i \in 1..N |-> "YES"]
  /\ sent = {}
  /\ rcvd = [i \in 1..N |-> {}]
  /\ fd = [i \in 1..N |-> FALSE]

UponYes(i) == 
  /\ pc[i] = "YES"
  /\ pc' = [pc EXCEPT ![i] = "SENT"]
  /\ sent' = sent \cup {"YES"}
  /\ rcvd' = rcvd
  /\ fd' = fd

UponNo(i) == 
  /\ pc[i] = "NO"
  /\ pc' = [pc EXCEPT ![i] = "SENT"]
  /\ sent' = sent \cup {"NO"}
  /\ rcvd' = rcvd
  /\ fd' = fd

UponSent(i) == 
  /\ pc[i] = "SENT"
  /\ (fd[i] = FALSE /\ "YES" \in rcvd[i]) => pc' = [pc EXCEPT ![i] = "COMMIT"]
  /\ (fd[i] = TRUE \/ "NO" \in rcvd[i]) => pc' = [pc EXCEPT ![i] = "ABORT"]
  /\ sent' = sent
  /\ rcvd' = rcvd
  /\ fd' = fd

UponCrash(i) == 
  /\ pc[i] /= "CRASH"
  /\ pc' = [pc EXCEPT ![i] = "CRASH"]
  /\ sent' = sent
  /\ rcvd' = rcvd
  /\ fd' = fd

Next == 
  \/ \E i \in 1..N : UponYes(i)
  \/ \E i \in 1..N : UponNo(i)
  \/ \E i \in 1..N : UponSent(i)
  \/ \E i \in 1..N : UponCrash(i)
  \/ (* do nothing *)
    pc' = pc
    /\ sent' = sent
    /\ rcvd' = [i \in 1..N |-> rcvd[i] \cup sent]
    /\ fd' = [i \in 1..N |-> fd[i] \lor (pc[i] = "CRASH")]

Spec == Init /\ [][Next]_<<pc, sent, rcvd, fd>>
          /\ WF_<<pc, sent, rcvd, fd>>(\E i \in 1..N : UponYes(i) \/ UponNo(i))
          /\ WF_<<pc, sent, rcvd, fd>>(\E i \in 1..N : UponSent(i))

TypeOK == 
  /\ pc \in [1..N -> {"YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH"}]
  /\ sent \subseteq {"YES", "NO"}
  /\ rcvd \in [1..N -> SUBSET {"YES", "NO"}]
  /\ fd \in [1..N -> BOOLEAN]

Validity == []<>(\A i \in 1..N : pc[i] = "COMMIT") => InitAllYes

THEOREM Spec => []TypeOK
THEOREM Spec => Validity
```