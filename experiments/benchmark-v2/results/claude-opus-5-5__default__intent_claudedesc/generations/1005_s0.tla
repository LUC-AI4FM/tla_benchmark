---------------------------- MODULE bcastFolklore ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME NTF == /\ N \in Nat /\ T \in Nat /\ F \in Nat
              /\ N > 2 * T
              /\ T >= F
              /\ F >= 0

VARIABLES Corr, nCrashed, pc, rcvd, sent

vars == << Corr, nCrashed, pc, rcvd, sent >>

Proc == 1 .. N
M    == { "ECHO" }
Msgs == Proc \X M
PCs  == { "V0", "V1", "AC", "CR" }

-----------------------------------------------------------------------------

Init ==
  /\ nCrashed = 0
  /\ Corr = Proc
  /\ sent = {}
  /\ pc \in [ Proc -> { "V0", "V1" } ]
  /\ rcvd = [ i \in Proc |-> {} ]

InitNoBcast == Init /\ pc = [ p \in Proc |-> "V0" ]

Receive(self, r) ==
  /\ self \in Corr
  /\ r \in sent
  /\ r \notin rcvd[self]
  /\ rcvd' = [ rcvd EXCEPT ![self] = @ \cup { r } ]
  /\ UNCHANGED << Corr, nCrashed, pc, sent >>

UponV1(self) ==
  /\ self \in Corr
  /\ pc[self] = "V1"
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { << self, "ECHO" >> }
  /\ UNCHANGED << Corr, nCrashed, rcvd >>

UponAccept(self) ==
  /\ self \in Corr
  /\ pc[self] \in { "V0", "V1" }
  /\ rcvd[self] # {}
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { << self, "ECHO" >> }
  /\ UNCHANGED << Corr, nCrashed, rcvd >>

Crash(self) ==
  /\ self \in Corr
  /\ pc[self] # "CR"
  /\ nCrashed < F
  /\ pc' = [ pc EXCEPT ![self] = "CR" ]
  /\ nCrashed' = nCrashed + 1
  /\ Corr' = Corr \ { self }
  /\ UNCHANGED << sent, rcvd >>

Step(self) ==
  \/ \E r \in Msgs : Receive(self, r)
  \/ UponV1(self)
  \/ UponAccept(self)
  \/ Crash(self)

Next == \E self \in Proc : Step(self)

Fairness ==
  \A p \in Proc :
     /\ WF_vars(\E r \in Msgs : Receive(p, r))
     /\ WF_vars(UponV1(p))
     /\ WF_vars(UponAccept(p))

Spec == Init /\ [][Next]_vars /\ Fairness

SpecNoBcast == InitNoBcast /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

TypeOK ==
  /\ Corr \subseteq Proc
  /\ nCrashed \in 0 .. N
  /\ pc \in [ Proc -> PCs ]
  /\ sent \subseteq Msgs
  /\ rcvd \in [ Proc -> SUBSET Msgs ]

CrashBound ==
  /\ nCrashed <= F
  /\ nCrashed <= T
  /\ Cardinality(Proc \ Corr) = nCrashed

CrashedStopped ==
  \A p \in Proc : (p \notin Corr) <=> (pc[p] = "CR")

MajorityCorrect == Cardinality(Corr) > N - Cardinality(Corr) - 1 /\ N > 2 * T

Unforgeability ==
  (\A i \in Proc : pc[i] = "V0") => [](\A i \in Corr : pc[i] # "AC")

Validity ==
  (\A i \in Corr : pc[i] = "V1") => <>(\E i \in Corr : pc[i] = "AC")

ValidityPerProc ==
  \A i \in Proc : [](pc[i] = "V1" => <>(pc[i] \in { "AC", "CR" }))

Agreement ==
  []((\E i \in Corr : pc[i] = "AC") => <>(\A i \in Corr : pc[i] = "AC"))

Termination ==
  <>[]( \/ \A i \in Corr : pc[i] = "AC"
        \/ \A i \in Corr : pc[i] = "V0" )

ReliableChan ==
  \A sndr \in Proc :
     []( << sndr, "ECHO" >> \in sent
           => <>[](\A p \in Corr : << sndr, "ECHO" >> \in rcvd[p]) )

=============================================================================