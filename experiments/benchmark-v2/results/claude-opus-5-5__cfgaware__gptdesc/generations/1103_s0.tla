------------------------------ MODULE nbacc_ray97 ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N >= 1

VARIABLES pc, rcvd, sent, fd

vars == << pc, rcvd, sent, fd >>

Proc == 1 .. N
M == { "YES", "NO" }
States == { "YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH" }

rcvd0 == [ i \in Proc |-> {} ]
sent0 == {}
fd0 == [ i \in Proc |-> FALSE ]

Init ==
  /\ pc \in [ Proc -> { "YES", "NO" } ]
  /\ sent = sent0
  /\ rcvd = rcvd0
  /\ fd = fd0

(* The process receives a new subset of messages that were sent *)
Receive(self) ==
  \E r \in SUBSET (Proc \X M):
     /\ r \subseteq sent
     /\ rcvd[self] \subseteq r
     /\ rcvd' = [ rcvd EXCEPT ![self] = r ]

(* The local failure detector nondeterministically reports a crash or not *)
FDUpdate(self) ==
  \E b \in BOOLEAN : fd' = [ fd EXCEPT ![self] = b ]

UponYes(self) ==
  /\ pc[self] = "YES"
  /\ pc' = [ pc EXCEPT ![self] = "SENT" ]
  /\ sent' = sent \cup { << self, "YES" >> }

UponNo(self) ==
  /\ pc[self] = "NO"
  /\ pc' = [ pc EXCEPT ![self] = "ABORT" ]
  /\ sent' = sent \cup { << self, "NO" >> }

UponCrash(self) ==
  /\ pc[self] \notin { "CRASH", "COMMIT", "ABORT" }
  /\ pc' = [ pc EXCEPT ![self] = "CRASH" ]
  /\ UNCHANGED sent

UponReceivingNoOrFD(self) ==
  /\ pc[self] = "SENT"
  /\ \/ \E p \in Proc : << p, "NO" >> \in rcvd'[self]
     \/ fd'[self] = TRUE
  /\ pc' = [ pc EXCEPT ![self] = "ABORT" ]
  /\ UNCHANGED sent

UponReceivingAllYes(self) ==
  /\ pc[self] = "SENT"
  /\ Cardinality({ p \in Proc : << p, "YES" >> \in rcvd'[self] }) = N
  /\ ~(\E p \in Proc : << p, "NO" >> \in rcvd'[self])
  /\ fd'[self] = FALSE
  /\ pc' = [ pc EXCEPT ![self] = "COMMIT" ]
  /\ UNCHANGED sent

NoLocalChange(self) ==
  /\ UNCHANGED << pc, sent >>

Step(self) ==
  /\ Receive(self)
  /\ FDUpdate(self)
  /\ \/ UponYes(self)
     \/ UponNo(self)
     \/ UponCrash(self)
     \/ UponReceivingNoOrFD(self)
     \/ UponReceivingAllYes(self)
     \/ NoLocalChange(self)

Next == \E self \in Proc : Step(self)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ pc \in [ Proc -> States ]
  /\ sent \subseteq (Proc \X M)
  /\ rcvd \in [ Proc -> SUBSET (Proc \X M) ]
  /\ fd \in [ Proc -> BOOLEAN ]

(* Validity: a commit is only possible if every process voted YES *)
Validity ==
  (\E i \in Proc : pc[i] = "COMMIT") =>
     (\A j \in Proc : << j, "YES" >> \in sent)

=============================================================================