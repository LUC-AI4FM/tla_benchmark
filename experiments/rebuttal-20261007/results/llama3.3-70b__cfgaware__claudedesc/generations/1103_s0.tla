---------------------------- MODULE NBAC ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE pc, sent, rcvd, fd

TypeOK == 
  /\ pc \in [1..N -> {"YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH"}]
  /\ sent \subseteq (1..N)
  /\ rcvd \in [1..N -> SUBSET (1..N)]
  /\ fd \in [1..N -> BOOLEAN]

Init == 
  /\ pc = [i \in 1..N |-> IF InitAllYes THEN "YES" ELSE CHOOSE {{ "YES", "NO" }}]
  /\ sent = {}
  /\ rcvd = [i \in 1..N |-> {}]
  /\ fd = [i \in 1..N |-> FALSE]

InitAllYes == TRUE

UponYes(i) == 
  /\ pc[i] = "YES"
  /\ pc' = [pc EXCEPT ![i] = "SENT"]
  /\ sent' = sent \cup {i}
  /\ UNCHANGED <<rcvd, fd>>

UponNo(i) == 
  /\ pc[i] = "NO"
  /\ pc' = [pc EXCEPT ![i] = "SENT"]
  /\ sent' = sent \cup {i}
  /\ UNCHANGED <<rcvd, fd>>

UponSent(i) == 
  /\ pc[i] = "SENT"
  /\ fd'[i] = FALSE
  /\ (\/ \A j \in 1..N : j \in rcvd'[i]
       /\ fd'[i] = FALSE
       /\ pc' = [pc EXCEPT ![i] = "COMMIT"]
      \/ ~(\A j \in 1..N : j \in rcvd'[i])
       /\ pc' = [pc EXCEPT ![i] = "ABORT"])
  /\ UNCHANGED sent

UponCrash(i) == 
  /\ pc[i] \in {"YES", "NO", "SENT"}
  /\ pc' = [pc EXCEPT ![i] = "CRASH"]
  /\ UNCHANGED <<sent, rcvd, fd>>

Next == 
  \/ \E i \in 1..N : UponYes(i)
  \/ \E i \in 1..N : UponNo(i)
  \/ \E i \in 1..N : UponSent(i)
  \/ \E i \in 1..N : UponCrash(i)
  \/ \E i \in 1..N, msg \subseteq sent :
      /\ pc' = pc
      /\ rcvd' = [rcvd EXCEPT ![i] = rcvd[i] \cup msg]
      /\ UNCHANGED <<sent, fd>>
  \/ \E i \in 1..N : 
      /\ pc' = pc
      /\ fd' = [fd EXCEPT ![i] = CHOOSE BOOLEAN]
      /\ UNCHANGED <<sent, rcvd>>

Spec == Init /\ [][Next]_<<pc, sent, rcvd, fd>>
           /\ WF_<<pc, sent, rcvd, fd>>(\E i \in 1..N : pc[i] = "YES" \/ pc[i] = "NO")
           /\ WF_<<pc, sent, rcvd, fd>>(\E i \in 1..N : pc[i] = "SENT")

Validity == []<>(\A i \in 1..N : pc[i] = "COMMIT") => InitAllYes

THEOREM Spec => []TypeOK
THEOREM Spec => Validity
====================================================================