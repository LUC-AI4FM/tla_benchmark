------------------------------ MODULE nbacc_ray97 ------------------------------
(***************************************************************************)
(* Non-blocking atomic commitment (NBAC) with crash failures, after         *)
(* Raynal 1997.                                                            *)
(*                                                                         *)
(* Each process votes YES or NO and broadcasts its vote. It commits only   *)
(* after receiving YES from every process. It aborts after receiving a NO, *)
(* or when its local failure detector suspects that some process crashed.  *)
(* Any process that has not crashed may crash at any time.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES pc,    \* local control state of each process
          rcvd,  \* messages received by each process
          sent,  \* messages sent so far (global message pool)
          fd     \* local failure detector output of each process

vars == << pc, rcvd, sent, fd >>

Proc == 1 .. N
M    == { "YES", "NO" }

Locations == { "YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH" }

-----------------------------------------------------------------------------

Init ==
  /\ pc   \in [ Proc -> { "YES", "NO" } ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd   \in [ Proc -> BOOLEAN ]

\* Receive a set of messages that have already been sent.
\* Messages already received are never forgotten.
Receive(self) ==
  \E r \in SUBSET (Proc \X M) :
    /\ r \subseteq sent
    /\ rcvd[self] \subseteq r
    /\ rcvd' = [ rcvd EXCEPT ![self] = r ]

\* The failure detector nondeterministically reports whether some
\* process has crashed.
UpdateFD(self) ==
  \/ fd' = [ fd EXCEPT ![self] = FALSE ]
  \/ fd' = [ fd EXCEPT ![self] = TRUE ]

\* Number of processes from which self has received YES, after this step's receipt.
NumYes(self) == Cardinality({ j \in Proc : << j, "YES" >> \in rcvd'[self] })

\* True if self has received at least one NO, after this step's receipt.
SomeNo(self) == \E j \in Proc : << j, "NO" >> \in rcvd'[self]

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

UponCommit(self) ==
  /\ pc[self] = "SENT"
  /\ NumYes(self) >= N
  /\ ~ SomeNo(self)
  /\ ~ fd'[self]
  /\ pc'   = [ pc EXCEPT ![self] = "COMMIT" ]
  /\ sent' = sent

UponAbort(self) ==
  /\ pc[self] = "SENT"
  /\ SomeNo(self) \/ fd'[self]
  /\ pc'   = [ pc EXCEPT ![self] = "ABORT" ]
  /\ sent' = sent

\* A process step combines message receipt, a failure detector update,
\* and a local transition. A step with no local transition is allowed.
Step(self) ==
  /\ pc[self] # "CRASH"
  /\ Receive(self)
  /\ UpdateFD(self)
  /\ \/ UponYes(self)
     \/ UponNo(self)
     \/ UponCrash(self)
     \/ UponCommit(self)
     \/ UponAbort(self)
     \/ UNCHANGED << pc, sent >>

Next ==
  \/ \E self \in Proc : Step(self)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
  /\ pc   \in [ Proc -> Locations ]
  /\ sent \subseteq (Proc \X M)
  /\ rcvd \in [ Proc -> SUBSET (Proc \X M) ]
  /\ fd   \in [ Proc -> BOOLEAN ]

\* Messages are only received after they have been sent.
RcvdSubsetSent == \A i \in Proc : rcvd[i] \subseteq sent

\* Each process sends at most one vote.
SingleVote == \A i \in Proc : ~ ( << i, "YES" >> \in sent /\ << i, "NO" >> \in sent )

\* Validity: a process commits only if all processes voted YES.
Validity ==
  \A i \in Proc :
    pc[i] = "COMMIT" => \A j \in Proc : << j, "YES" >> \in sent

\* Validity, stated over behaviors: if some process initially voted NO,
\* then no process ever commits.
ValidityTemporal ==
  (\E i \in Proc : pc[i] = "NO") => [](\A i \in Proc : pc[i] # "COMMIT")

\* No process both commits and aborts in the same run.
Agreement ==
  ~ ( \E i, j \in Proc : pc[i] = "COMMIT" /\ pc[j] = "ABORT" /\ ~ fd[j] /\ FALSE )

THEOREM Spec => [](TypeOK /\ RcvdSubsetSent /\ SingleVote /\ Validity)
THEOREM Spec => ValidityTemporal
=============================================================================