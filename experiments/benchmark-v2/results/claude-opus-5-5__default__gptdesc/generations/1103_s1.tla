------------------------------ MODULE nbacc_ray97 ------------------------------
(***************************************************************************)
(* Non-blocking atomic commitment (NBAC) with crash failures, after        *)
(* Raynal 1997.                                                            *)
(*                                                                         *)
(* Each process votes YES or NO and broadcasts its vote. A process may     *)
(* crash at any time. Each process has a local failure detector that may   *)
(* nondeterministically report that some process has crashed.             *)
(*                                                                         *)
(* A process that has sent its vote:                                       *)
(*   - commits once it has received YES from every process;                *)
(*   - aborts if it has received NO from some process;                     *)
(*   - aborts if its failure detector reports a crash.                     *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES pc, rcvd, sent, fd

vars == << pc, rcvd, sent, fd >>

Proc == 1 .. N

M == { "YES", "NO" }

Status == { "YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH" }

Init ==
  /\ pc \in [ Proc -> { "YES", "NO" } ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd = [ i \in Proc |-> FALSE ]

(* Receive a new subset of the messages sent so far *)
Receive(self) ==
  \E r \in SUBSET sent :
     /\ rcvd[self] \subseteq r
     /\ rcvd' = [ rcvd EXCEPT ![self] = r ]

(* The failure detector nondeterministically reports a crash or not *)
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
  /\ pc[self] \notin { "CRASH" }
  /\ pc' = [ pc EXCEPT ![self] = "CRASH" ]
  /\ sent' = sent

UponReceivingYesFromAll(self) ==
  /\ pc[self] = "SENT"
  /\ \A i \in Proc : << i, "YES" >> \in rcvd'[self]
  /\ pc' = [ pc EXCEPT ![self] = "COMMIT" ]
  /\ sent' = sent

UponReceivingNo(self) ==
  /\ pc[self] = "SENT"
  /\ \E i \in Proc : << i, "NO" >> \in rcvd'[self]
  /\ pc' = [ pc EXCEPT ![self] = "ABORT" ]
  /\ sent' = sent

UponFailureDetected(self) ==
  /\ pc[self] = "SENT"
  /\ fd'[self] = TRUE
  /\ pc' = [ pc EXCEPT ![self] = "ABORT" ]
  /\ sent' = sent

Stay(self) ==
  /\ pc' = pc
  /\ sent' = sent

(* A step combines receipt, a failure detector update, and a local transition *)
Step(self) ==
  /\ pc[self] # "CRASH"
  /\ Receive(self)
  /\ UpdateFailureDetector(self)
  /\ \/ UponYes(self)
     \/ UponNo(self)
     \/ UponCrash(self)
     \/ UponReceivingYesFromAll(self)
     \/ UponReceivingNo(self)
     \/ UponFailureDetected(self)
     \/ Stay(self)

Next ==
  \/ \E self \in Proc : Step(self)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK ==
  /\ pc \in [ Proc -> Status ]
  /\ sent \subseteq (Proc \X M)
  /\ rcvd \in [ Proc -> SUBSET (Proc \X M) ]
  /\ fd \in [ Proc -> BOOLEAN ]

(* Validity: a process can only commit if every process voted YES. *)
Validity ==
  (\E i \in Proc : pc[i] = "COMMIT") => (\A j \in Proc : << j, "YES" >> \in sent)

(* No process ever commits if some process voted NO. *)
NoCommitOnNo ==
  (\E j \in Proc : << j, "NO" >> \in sent) => (\A i \in Proc : pc[i] # "COMMIT")

(* Received messages are always messages that were actually sent. *)
RcvdSubsetSent ==
  \A i \in Proc : rcvd[i] \subseteq sent

=============================================================================