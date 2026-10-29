---------------------------- MODULE nbacc_ray97 ----------------------------
(***************************************************************************)
(* Non-blocking atomic commitment (NBAC) with crash failures, following    *)
(* Raynal 1997.  Every process votes YES or NO, broadcasts its vote, may   *)
(* crash at any time, and consults a local failure detector that can       *)
(* nondeterministically report that some process has crashed.             *)
(*                                                                         *)
(* A process commits once it has received YES from every process.  It      *)
(* aborts once it has received some NO or its failure detector reports a   *)
(* crash.                                                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES
    pc,     \* local state of each process
    rcvd,   \* messages received by each process
    sent,   \* set of messages broadcast so far: <<sender, value>>
    fd      \* local failure detector output of each process

vars == << pc, rcvd, sent, fd >>

Proc   == 1 .. N
Votes  == { "YES", "NO" }
M      == { "YES", "NO" }
States == { "YES", "NO", "SENT_YES", "SENT_NO", "COMMIT", "ABORT", "CRASH" }

-----------------------------------------------------------------------------
(* Initialization: every process votes YES or NO; there are no messages,   *)
(* and the failure detectors start in an arbitrary state.                  *)

Init ==
    /\ pc   \in [ Proc -> Votes ]
    /\ sent = {}
    /\ rcvd = [ i \in Proc |-> {} ]
    /\ fd   \in [ Proc -> BOOLEAN ]

-----------------------------------------------------------------------------
(* Message receipt: a process receives some subset of the sent messages    *)
(* that includes everything it has already received.                      *)

Receive(self) ==
    \E r \in SUBSET (Proc \X M) :
        /\ r \subseteq sent
        /\ rcvd[self] \subseteq r
        /\ rcvd' = [ rcvd EXCEPT ![self] = r ]

(* Failure detector update: the local detector nondeterministically        *)
(* reports or does not report that some process has crashed.               *)

UpdateFailureDetector(self) ==
    \/ fd' = [ fd EXCEPT ![self] = FALSE ]
    \/ fd' = [ fd EXCEPT ![self] = TRUE ]

-----------------------------------------------------------------------------
(* Local transitions *)

UponYes(self) ==
    /\ pc[self] = "YES"
    /\ pc'   = [ pc EXCEPT ![self] = "SENT_YES" ]
    /\ sent' = sent \cup { << self, "YES" >> }

UponNo(self) ==
    /\ pc[self] = "NO"
    /\ pc'   = [ pc EXCEPT ![self] = "SENT_NO" ]
    /\ sent' = sent \cup { << self, "NO" >> }

UponCrash(self) ==
    /\ pc[self] \notin { "CRASH", "COMMIT", "ABORT" }
    /\ pc'   = [ pc EXCEPT ![self] = "CRASH" ]
    /\ sent' = sent

RcvdYesFrom(self) == { p \in Proc : << p, "YES" >> \in rcvd'[self] }
RcvdSomeNo(self)  == \E p \in Proc : << p, "NO" >> \in rcvd'[self]

UponReceivedAllYes(self) ==
    /\ pc[self] = "SENT_YES"
    /\ Cardinality(RcvdYesFrom(self)) = N
    /\ ~RcvdSomeNo(self)
    /\ ~fd'[self]
    /\ pc'   = [ pc EXCEPT ![self] = "COMMIT" ]
    /\ sent' = sent

UponReceivedSomeNo(self) ==
    /\ pc[self] \in { "SENT_YES", "SENT_NO" }
    /\ RcvdSomeNo(self)
    /\ pc'   = [ pc EXCEPT ![self] = "ABORT" ]
    /\ sent' = sent

UponFailureDetected(self) ==
    /\ pc[self] \in { "SENT_YES", "SENT_NO" }
    /\ fd'[self]
    /\ pc'   = [ pc EXCEPT ![self] = "ABORT" ]
    /\ sent' = sent

-----------------------------------------------------------------------------
(* A step of a process: receive messages, update the failure detector and  *)
(* perform a local transition, or stay idle.                               *)

Step(self) ==
    /\ Receive(self)
    /\ UpdateFailureDetector(self)
    /\ \/ UponYes(self)
       \/ UponNo(self)
       \/ UponCrash(self)
       \/ UponReceivedAllYes(self)
       \/ UponReceivedSomeNo(self)
       \/ UponFailureDetected(self)
       \/ UNCHANGED << pc, sent >>

Next == (\E self \in Proc : Step(self)) \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ pc   \in [ Proc -> States ]
    /\ sent \subseteq (Proc \X M)
    /\ rcvd \in [ Proc -> SUBSET (Proc \X M) ]
    /\ fd   \in [ Proc -> BOOLEAN ]

(* Validity: a process may commit only if every process voted YES.        *)
Validity ==
    (\E i \in Proc : pc[i] = "COMMIT") => (\A j \in Proc : << j, "YES" >> \in sent)

(* No process that broadcast NO ever reaches COMMIT; a commit is only      *)
(* possible when the votes are unanimously YES.                           *)
NoCommitOnNo ==
    (\E j \in Proc : << j, "NO" >> \in sent) => (\A i \in Proc : pc[i] # "COMMIT")

THEOREM Spec => [](TypeOK /\ Validity /\ NoCommitOnNo)

=============================================================================