---- MODULE nbacc_ray97 ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES pc, rcvd, sent, fd

vars == << pc, rcvd, sent, fd >>

Proc == 1 .. N

M == { "YES", "NO" }

States == { "YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH" }

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> { "YES", "NO" } ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd \in [ Proc -> { FALSE } ]

InitAllYes ==
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "YES" ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd \in [ Proc -> { FALSE } ]

Receive(self) ==
  \E r \in SUBSET (Proc \X M) :
    /\ r \subseteq sent
    /\ rcvd' = [ rcvd EXCEPT ![self] = rcvd[self] \cup r ]

UpdateFailureDetector(self) ==
  \/ fd' = [ fd EXCEPT ![self] = FALSE ]
  \/ fd' = [ fd EXCEPT ![self] = TRUE ]

UponYes(self) ==
  /\ pc[self] = "YES"
  /\ pc' = [ pc EXCEPT ![self] = "SENT" ]
  /\ sent' = sent \cup { << self, "YES" >> }

UponNo(self) ==
  /\ pc[self] = "NO"
  /\ pc' = [ pc EXCEPT ![self] = "SENT" ]
  /\ sent' = sent \cup { << self, "NO" >> }

UponCrash(self) ==
  /\ pc[self] # "CRASH"
  /\ pc' = [ pc EXCEPT ![self] = "CRASH" ]
  /\ sent' = sent

AllYesReceived(self) ==
  \A i \in Proc : << i, "YES" >> \in rcvd'[self]

UponSent(self) ==
  /\ pc[self] = "SENT"
  /\ IF fd'[self] = FALSE /\ AllYesReceived(self)
       THEN pc' = [ pc EXCEPT ![self] = "COMMIT" ]
       ELSE pc' = [ pc EXCEPT ![self] = "ABORT" ]
  /\ sent' = sent

Step(self) ==
  /\ Receive(self)
  /\ UpdateFailureDetector(self)
  /\ \/ UponYes(self)
     \/ UponNo(self)
     \/ UponCrash(self)
     \/ UponSent(self)
     \/ UNCHANGED << pc, sent >>

Next == (\E self \in Proc : Step(self)) \/ UNCHANGED vars

FairStep(self) ==
  /\ pc[self] # "CRASH"
  /\ Receive(self)
  /\ UpdateFailureDetector(self)
  /\ \/ UponYes(self)
     \/ UponNo(self)
     \/ UponSent(self)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E self \in Proc : FairStep(self))

TypeOK ==
  /\ sent \subseteq Proc \X M
  /\ pc \in [ Proc -> States ]
  /\ rcvd \in [ Proc -> SUBSET sent ]
  /\ fd \in [ Proc -> BOOLEAN ]

Validity ==
  (\E i \in Proc : pc[i] = "NO") => [](\A j \in Proc : pc[j] # "COMMIT")

====