---------------------------- MODULE nbacg_guer01 ----------------------------
(***************************************************************************)
(* Parameterized asynchronous non-blocking atomic commitment (NBAC) with  *)
(* failure detectors, after Guerraoui's "On the hardness of failure-       *)
(* sensitive agreement problems".                                          *)
(*                                                                         *)
(* Each process votes YES or NO and broadcasts its vote. It may crash, and *)
(* its failure detector may suspect other processes. A process that has    *)
(* voted aborts if it receives a NO vote or suspects a crash. It commits   *)
(* if it receives YES from every process and suspects nobody.              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES
  pc,     \* control location of each process
  rcvd,   \* set of messages received by each process
  sent,   \* set of messages sent so far
  fd      \* fd[p] = TRUE iff the failure detector of p currently suspects a crash

vars == << pc, rcvd, sent, fd >>

Proc     == 1 .. N
Status   == { "YES", "NO" }
Location == { "YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH" }
Msg      == Proc \X Status

(***************************************************************************)
(* Process self receives some messages that were sent. Received messages  *)
(* are never forgotten.                                                    *)
(***************************************************************************)
Receive(self) ==
  \E r \in SUBSET Msg :
    /\ r \subseteq sent
    /\ rcvd[self] \subseteq r
    /\ rcvd' = [rcvd EXCEPT ![self] = r]

(***************************************************************************)
(* The failure detector of self gives a new, nondeterministic prediction. *)
(***************************************************************************)
UpdateFailureDetector(self) ==
  \/ fd' = [fd EXCEPT ![self] = FALSE]
  \/ fd' = [fd EXCEPT ![self] = TRUE]

(* Process self crashes. *)
UponCrash(self) ==
  /\ pc[self] # "CRASH"
  /\ pc' = [pc EXCEPT ![self] = "CRASH"]
  /\ sent' = sent

(* Process self broadcasts its YES vote. *)
UponYes(self) ==
  /\ pc[self] = "YES"
  /\ pc' = [pc EXCEPT ![self] = "SENT"]
  /\ sent' = sent \cup { << self, "YES" >> }

(* Process self broadcasts its NO vote. *)
UponNo(self) ==
  /\ pc[self] = "NO"
  /\ pc' = [pc EXCEPT ![self] = "SENT"]
  /\ sent' = sent \cup { << self, "NO" >> }

(***************************************************************************)
(* The process has voted and received YES from every process while        *)
(* suspecting nobody, so it commits.                                       *)
(***************************************************************************)
UponReceivingAllYesNoSuspicion(self) ==
  /\ pc[self] = "SENT"
  /\ fd'[self] = FALSE
  /\ \A i \in Proc : << i, "YES" >> \in rcvd'[self]
  /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
  /\ sent' = sent

(***************************************************************************)
(* The process has voted and either received a NO vote or suspects some   *)
(* process, so it aborts.                                                  *)
(***************************************************************************)
UponNoOrSuspicion(self) ==
  /\ pc[self] = "SENT"
  /\ \/ fd'[self] = TRUE
     \/ \E i \in Proc : << i, "NO" >> \in rcvd'[self]
  /\ pc' = [pc EXCEPT ![self] = "ABORT"]
  /\ sent' = sent

(* One step of process self. Crashed processes take no further steps. *)
Step(self) ==
  /\ pc[self] # "CRASH"
  /\ Receive(self)
  /\ UpdateFailureDetector(self)
  /\ \/ UponYes(self)
     \/ UponNo(self)
     \/ UponReceivingAllYesNoSuspicion(self)
     \/ UponNoOrSuspicion(self)
     \/ UponCrash(self)
     \/ UNCHANGED << pc, sent >>

(* Initially every process votes YES or NO, and nothing is sent or received. *)
Init ==
  /\ pc \in [Proc -> Status]
  /\ sent = {}
  /\ rcvd = [i \in Proc |-> {}]
  /\ fd = [i \in Proc |-> FALSE]

(* Specialized initial condition: every process votes YES. *)
InitAllYes ==
  /\ pc = [i \in Proc |-> "YES"]
  /\ sent = {}
  /\ rcvd = [i \in Proc |-> {}]
  /\ fd = [i \in Proc |-> FALSE]

(* Specialized initial condition: every process votes NO. *)
InitAllNo ==
  /\ pc = [i \in Proc |-> "NO"]
  /\ sent = {}
  /\ rcvd = [i \in Proc |-> {}]
  /\ fd = [i \in Proc |-> FALSE]

Next == \E self \in Proc : Step(self)

(* Weak fairness applies to the non-stuttering steps of each process. *)
Fairness == \A self \in Proc : WF_vars(Step(self) /\ vars' # vars)

Spec       == Init       /\ [][Next]_vars /\ Fairness
SpecAllYes == InitAllYes /\ [][Next]_vars /\ Fairness
SpecAllNo  == InitAllNo  /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ pc \in [Proc -> Location]
  /\ sent \subseteq Msg
  /\ rcvd \in [Proc -> SUBSET Msg]
  /\ \A i \in Proc : rcvd[i] \subseteq sent
  /\ fd \in [Proc -> BOOLEAN]

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

(* No two processes decide differently. *)
Agreement ==
  [](\A i, j \in Proc : ~(pc[i] = "COMMIT" /\ pc[j] = "ABORT"))

(* If some process votes NO, then no process ever commits. *)
AbortValidity ==
  (\E i \in Proc : pc[i] = "NO") => [](\A j \in Proc : pc[j] # "COMMIT")

(***************************************************************************)
(* If every process votes YES and no process ever crashes, then no process *)
(* ever aborts.                                                            *)
(***************************************************************************)
CommitValidity ==
  ( /\ \A i \in Proc : pc[i] = "YES"
    /\ [](\A i \in Proc : pc[i] # "CRASH") )
    => [](\A j \in Proc : pc[j] # "ABORT")

(* Every process eventually decides or crashes. *)
Termination ==
  <>(\A i \in Proc : pc[i] \in { "COMMIT", "ABORT", "CRASH" })

(***************************************************************************)
(* Eventual commit: if every process votes YES, none crashes, and the      *)
(* failure detectors eventually stop suspecting, then every process        *)
(* eventually commits.                                                     *)
(***************************************************************************)
EventualCommit ==
  ( /\ \A i \in Proc : pc[i] = "YES"
    /\ [](\A i \in Proc : pc[i] # "CRASH")
    /\ <>[](\A i \in Proc : fd[i] = FALSE) )
    => <>(\A i \in Proc : pc[i] = "COMMIT")

=============================================================================