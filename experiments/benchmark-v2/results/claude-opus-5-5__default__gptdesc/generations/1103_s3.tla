------------------------------ MODULE nbacc_ray97 ------------------------------
(***************************************************************************)
(* Non-blocking atomic commitment (NBAC) with crash failures, based on     *)
(* Raynal 1997.  Processes vote YES or NO, broadcast their votes, may      *)
(* crash, and query a local failure detector that may nondeterministically *)
(* report that some process has crashed.                                   *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES pc,     \* program counter (local state) of each process
          rcvd,   \* messages received by each process
          sent,   \* messages sent by all processes
          fd      \* local failure detector output of each process

ASSUME N \in Nat

Proc == 1 .. N
M == { "YES", "NO" }

vars == << pc, rcvd, sent, fd >>

States == { "YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH" }

Init ==
  /\ pc \in [ Proc -> { "YES", "NO" } ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd = [ i \in Proc |-> FALSE ]

(* A process receives a new subset of sent messages (monotonically). *)
Receive(self) ==
  \E r \in SUBSET (Proc \X M) :
    /\ r \subseteq sent
    /\ rcvd[self] \subseteq r
    /\ rcvd' = [ rcvd EXCEPT ![self] = r ]

(* The local failure detector nondeterministically reports a failure or not. *)
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

UponReceivingAllYes(self) ==
  /\ pc[self] = "SENT"
  /\ fd'[self] = FALSE
  /\ Cardinality({ p \in Proc : << p, "YES" >> \in rcvd'[self] }) = N
  /\ pc' = [ pc EXCEPT ![self] = "COMMIT" ]
  /\ sent' = sent

UponReceivingNo(self) ==
  /\ pc[self] = "SENT"
  /\ \E p \in Proc : << p, "NO" >> \in rcvd'[self]
  /\ pc' = [ pc EXCEPT ![self] = "ABORT" ]
  /\ sent' = sent

UponFailureDetected(self) ==
  /\ pc[self] = "SENT"
  /\ fd'[self] = TRUE
  /\ pc' = [ pc EXCEPT ![self] = "ABORT" ]
  /\ sent' = sent

LocalNoOp(self) ==
  /\ pc' = pc
  /\ sent' = sent

Step(self) ==
  /\ Receive(self)
  /\ UpdateFailureDetector(self)
  /\ \/ UponYes(self)
     \/ UponNo(self)
     \/ UponCrash(self)
     \/ UponReceivingAllYes(self)
     \/ UponReceivingNo(self)
     \/ UponFailureDetected(self)
     \/ LocalNoOp(self)

Next == \E self \in Proc : Step(self)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

TypeOK ==
  /\ pc \in [ Proc -> States ]
  /\ sent \subseteq (Proc \X M)
  /\ rcvd \in [ Proc -> SUBSET (Proc \X M) ]
  /\ fd \in [ Proc -> BOOLEAN ]

(* A process may commit only if every process voted YES. *)
Validity ==
  (\E i \in Proc : pc[i] = "COMMIT")
    => (\A j \in Proc : << j, "YES" >> \in sent)

(* As long as all processes still hold a unanimous YES vote, nobody aborts. *)
UnanimousYesNoAbort ==
  (\A i \in Proc : pc[i] = "YES") => (\A i \in Proc : pc[i] # "ABORT")

=============================================================================