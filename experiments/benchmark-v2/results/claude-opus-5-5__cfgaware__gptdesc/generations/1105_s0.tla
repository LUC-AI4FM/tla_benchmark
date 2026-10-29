------------------------------ MODULE nbacg_guer01 ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES pc, rcvd, sent, fd

ASSUME NType == N \in Nat /\ N >= 1

Proc == 1 .. N

M == { "YES", "NO" }

Location == { "YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH" }

vars == << pc, rcvd, sent, fd >>

\* number of YES / NO messages received by self in the next state
rcvd_yes(self) == Cardinality({ m \in rcvd'[self] : m[2] = "YES" })
rcvd_no(self)  == Cardinality({ m \in rcvd'[self] : m[2] = "NO" })

\* self receives a (possibly empty) set of new messages among the sent ones
Receive(self) ==
  \E r \in SUBSET (Proc \X M) :
     /\ r \subseteq sent
     /\ rcvd[self] \subseteq r
     /\ rcvd' = [rcvd EXCEPT ![self] = r]

\* a process that voted YES broadcasts its vote
UponYes(self) ==
  /\ pc[self] = "YES"
  /\ pc' = [pc EXCEPT ![self] = "SENT"]
  /\ sent' = sent \cup { << self, "YES" >> }
  /\ UNCHANGED fd

\* a process that voted NO broadcasts its vote and aborts
UponNo(self) ==
  /\ pc[self] = "NO"
  /\ pc' = [pc EXCEPT ![self] = "ABORT"]
  /\ sent' = sent \cup { << self, "NO" >> }
  /\ UNCHANGED fd

\* a process crashes
UponCrash(self) ==
  /\ pc[self] \notin { "CRASH" }
  /\ pc' = [pc EXCEPT ![self] = "CRASH"]
  /\ UNCHANGED << sent, fd >>

\* a process received YES from all processes and commits
UponReceivingYesFromAll(self) ==
  /\ pc[self] = "SENT"
  /\ rcvd_yes(self) >= N
  /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
  /\ UNCHANGED << sent, fd >>

\* a process received a NO vote and aborts
UponReceivingNo(self) ==
  /\ pc[self] = "SENT"
  /\ rcvd_no(self) >= 1
  /\ pc' = [pc EXCEPT ![self] = "ABORT"]
  /\ UNCHANGED << sent, fd >>

\* the failure detector of self suspects some process; self aborts
UponSuspicion(self) ==
  /\ pc[self] = "SENT"
  /\ fd' = [fd EXCEPT ![self] = TRUE]
  /\ pc' = [pc EXCEPT ![self] = "ABORT"]
  /\ UNCHANGED sent

\* progress actions (no crashes, no stuttering)
Progress(self) ==
  /\ Receive(self)
  /\ \/ UponYes(self)
     \/ UponNo(self)
     \/ UponReceivingYesFromAll(self)
     \/ UponReceivingNo(self)
     \/ UponSuspicion(self)

Step(self) ==
  \/ Progress(self)
  \/ /\ UNCHANGED rcvd
     /\ UponCrash(self)
  \/ /\ Receive(self)
     /\ UNCHANGED << pc, sent, fd >>

Init ==
  /\ pc \in [ Proc -> { "YES", "NO" } ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd = [ i \in Proc |-> FALSE ]

\* specialized initial conditions
InitAllYes ==
  /\ pc = [ i \in Proc |-> "YES" ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd = [ i \in Proc |-> FALSE ]

InitAllNo ==
  /\ pc = [ i \in Proc |-> "NO" ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd = [ i \in Proc |-> FALSE ]

Next == \E self \in Proc : Step(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E self \in Proc : Progress(self))

SpecAllYes == InitAllYes /\ [][Next]_vars /\ WF_vars(\E self \in Proc : Progress(self))

SpecAllNo == InitAllNo /\ [][Next]_vars /\ WF_vars(\E self \in Proc : Progress(self))

TypeOK ==
  /\ pc \in [ Proc -> Location ]
  /\ sent \subseteq (Proc \X M)
  /\ rcvd \in [ Proc -> SUBSET (Proc \X M) ]
  /\ fd \in [ Proc -> BOOLEAN ]

\* no two processes decide differently
AgrrLtl ==
  [](~(\E i \in Proc, j \in Proc : pc[i] = "COMMIT" /\ pc[j] = "ABORT"))

\* if some process votes NO, no process ever commits
AbortValidityLtl ==
  (\E i \in Proc : pc[i] = "NO") => [](\A i \in Proc : pc[i] # "COMMIT")

\* if all vote YES and there are neither crashes nor suspicions, all commit
CommitValidityLtl ==
  ( /\ (\A i \in Proc : pc[i] = "YES")
    /\ [](\A i \in Proc : pc[i] # "CRASH" /\ fd[i] = FALSE) )
  => <>(\A i \in Proc : pc[i] = "COMMIT")

\* every correct process eventually decides
TerminationLtl ==
  <>(\A i \in Proc : pc[i] \in { "COMMIT", "ABORT", "CRASH" })

\* eventually some process commits
CommitLtl ==
  <>(\E i \in Proc : pc[i] = "COMMIT")

=============================================================================