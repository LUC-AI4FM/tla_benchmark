------------------------------ MODULE nbacc_ray97 ------------------------------
(***************************************************************************)
(* Non-blocking atomic commitment (NBAC) with crash failures, following    *)
(* Raynal 1997.  Every process votes YES or NO and broadcasts its vote.    *)
(* Processes may crash.  Each process has a local failure detector that    *)
(* may nondeterministically report that some process has crashed.          *)
(*                                                                         *)
(*  - A process that receives a NO vote aborts.                            *)
(*  - A process that receives YES votes from all processes commits.        *)
(*  - A process whose failure detector reports a crash aborts.             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES
  pc,     \* local control state of every process
  rcvd,   \* messages received by every process
  sent,   \* messages broadcast so far (set of <<sender, vote>>)
  fd      \* local failure detector output of every process

vars == << pc, rcvd, sent, fd >>

Proc   == 1 .. N
M      == { "YES", "NO" }
Status == { "YES", "NO", "SENT", "CRASH", "COMMIT", "ABORT" }

(***************************************************************************)
(* Initial states                                                          *)
(***************************************************************************)
Init ==
  /\ pc   \in [ Proc -> { "YES", "NO" } ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd   \in [ Proc -> BOOLEAN ]

(***************************************************************************)
(* Message receipt: a process receives some of the messages sent so far,   *)
(* never losing what it has already received.                              *)
(***************************************************************************)
Receive(self) ==
  \E r \in SUBSET (Proc \X M) :
    /\ r \subseteq sent
    /\ rcvd[self] \subseteq r
    /\ rcvd' = [ rcvd EXCEPT ![self] = r ]

(***************************************************************************)
(* Failure detector: nondeterministically reports whether some process     *)
(* has crashed.                                                            *)
(***************************************************************************)
UpdateFD(self) ==
  \/ fd' = [ fd EXCEPT ![self] = FALSE ]
  \/ fd' = [ fd EXCEPT ![self] = TRUE ]

(***************************************************************************)
(* Local transitions                                                       *)
(***************************************************************************)
UponYes(self) ==
  /\ pc[self] = "YES"
  /\ pc'   = [ pc EXCEPT ![self] = "SENT" ]
  /\ sent' = sent \cup { << self, "YES" >> }

UponNo(self) ==
  /\ pc[self] = "NO"
  /\ pc'   = [ pc EXCEPT ![self] = "SENT" ]
  /\ sent' = sent \cup { << self, "NO" >> }

UponCrash(self) ==
  /\ pc[self] \notin { "CRASH" }
  /\ pc'   = [ pc EXCEPT ![self] = "CRASH" ]
  /\ sent' = sent

UponReceivingNo(self) ==
  /\ pc[self] = "SENT"
  /\ \E j \in Proc : << j, "NO" >> \in rcvd'[self]
  /\ pc'   = [ pc EXCEPT ![self] = "ABORT" ]
  /\ sent' = sent

UponReceivingYesFromAll(self) ==
  /\ pc[self] = "SENT"
  /\ \A j \in Proc : << j, "YES" >> \in rcvd'[self]
  /\ ~ fd'[self]
  /\ pc'   = [ pc EXCEPT ![self] = "COMMIT" ]
  /\ sent' = sent

UponFailure(self) ==
  /\ pc[self] = "SENT"
  /\ fd'[self]
  /\ pc'   = [ pc EXCEPT ![self] = "ABORT" ]
  /\ sent' = sent

(***************************************************************************)
(* A step of a process: receive messages, update the failure detector,     *)
(* then perform a local transition (or stutter locally).                   *)
(***************************************************************************)
Step(self) ==
  /\ Receive(self)
  /\ UpdateFD(self)
  /\ \/ UponYes(self)
     \/ UponNo(self)
     \/ UponCrash(self)
     \/ UponReceivingNo(self)
     \/ UponReceivingYesFromAll(self)
     \/ UponFailure(self)
     \/ UNCHANGED << pc, sent >>

Next == \E self \in Proc : Step(self)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
  /\ pc   \in [ Proc -> Status ]
  /\ sent \subseteq (Proc \X M)
  /\ rcvd \in [ Proc -> SUBSET (Proc \X M) ]
  /\ fd   \in [ Proc -> BOOLEAN ]

\* Received messages were actually sent.
RcvdSent == \A i \in Proc : rcvd[i] \subseteq sent

\* Validity: a process may commit only if all processes voted YES.
Validity ==
  \A i \in Proc :
    pc[i] = "COMMIT" => \A j \in Proc : << j, "YES" >> \in sent

\* No process that commits coexists with a NO vote.
NoCommitWithNo ==
  (\E i \in Proc : pc[i] = "COMMIT") => \A j \in Proc : << j, "NO" >> \notin sent

\* Temporal form of validity: if some process initially votes NO,
\* then no process ever commits.
ValidityTemporal ==
  (\E i \in Proc : pc[i] = "NO") => [](\A i \in Proc : pc[i] # "COMMIT")

THEOREM Spec => [](TypeOK /\ RcvdSent /\ Validity /\ NoCommitWithNo)
=============================================================================