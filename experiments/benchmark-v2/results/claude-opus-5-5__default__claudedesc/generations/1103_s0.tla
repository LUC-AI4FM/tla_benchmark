------------------------------ MODULE nbacc_ray97 ------------------------------
(* Non-Blocking Atomic Commitment with crash failures, after Raynal (1997). *)

EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES pc,    \* program counter of each process
          rcvd,  \* messages received by each process
          sent,  \* global set of messages sent so far
          fd     \* failure detector reading of each process (TRUE = a crash is suspected)

vars == << pc, rcvd, sent, fd >>

Proc == 1 .. N
M    == { "YES", "NO" }
States == { "YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH" }

-----------------------------------------------------------------------------

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> { "YES", "NO" } ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd = [ i \in Proc |-> FALSE ]

InitAllYes ==
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "YES" ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd = [ i \in Proc |-> FALSE ]

(* The process receives a subset of the sent messages. Received messages
   accumulate: it keeps everything it received earlier. *)
Receive(self) ==
  \E r \in SUBSET (Proc \X M) :
     /\ r \subseteq sent
     /\ rcvd[self] \subseteq r
     /\ rcvd' = [ rcvd EXCEPT ![self] = r ]

(* The failure detector nondeterministically reports whether some process
   has crashed. *)
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

AllYesReceived(self) ==
  \A p \in Proc : << p, "YES" >> \in rcvd'[self]

UponSent(self) ==
  /\ pc[self] = "SENT"
  /\ \/ /\ fd'[self] = FALSE
        /\ AllYesReceived(self)
        /\ pc' = [ pc EXCEPT ![self] = "COMMIT" ]
     \/ /\ \/ fd'[self] = TRUE
           \/ ~AllYesReceived(self)
        /\ pc' = [ pc EXCEPT ![self] = "ABORT" ]
  /\ sent' = sent

UponCrash(self) ==
  /\ pc[self] # "CRASH"
  /\ pc' = [ pc EXCEPT ![self] = "CRASH" ]
  /\ sent' = sent

Step(self) ==
  /\ Receive(self)
  /\ UpdateFailureDetector(self)
  /\ \/ UponYes(self)
     \/ UponNo(self)
     \/ UponSent(self)
     \/ UponCrash(self)
     \/ UNCHANGED << pc, sent >>

Next == \/ \E self \in Proc : Step(self)
        \/ UNCHANGED vars

(* Fairness: non-crashed processes eventually send their votes and
   attempt to decide. *)
Progress ==
  \E self \in Proc :
     /\ pc[self] # "CRASH"
     /\ Receive(self)
     /\ UpdateFailureDetector(self)
     /\ \/ UponYes(self)
        \/ UponNo(self)
        \/ UponSent(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(Progress)

SpecAllYes == InitAllYes /\ [][Next]_vars /\ WF_vars(Progress)

-----------------------------------------------------------------------------

TypeOK ==
  /\ sent \subseteq Proc \X M
  /\ pc \in [ Proc -> States ]
  /\ rcvd \in [ Proc -> SUBSET (Proc \X M) ]
  /\ fd \in [ Proc -> BOOLEAN ]

(* A commit decision is possible only if every process initially voted YES. *)
Validity ==
  (\E i \in Proc : pc[i] = "NO") => [](\A i \in Proc : pc[i] # "COMMIT")

=============================================================================