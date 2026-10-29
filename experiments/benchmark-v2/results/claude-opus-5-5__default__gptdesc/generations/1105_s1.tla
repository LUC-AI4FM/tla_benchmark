------------------------------ MODULE nbacg_guer01 ------------------------------
(***************************************************************************)
(* Parameterized asynchronous non-blocking atomic commitment (NBAC) with   *)
(* failure detectors, after Guerraoui's failure-sensitive agreement paper. *)
(*                                                                         *)
(* Each process votes YES or NO, broadcasts its vote, and receives votes.  *)
(* A process aborts if it receives a NO vote, or if its failure detector   *)
(* suspects some process before it has received all N YES votes. It       *)
(* commits once it has received YES votes from all N processes. A process  *)
(* may crash at any time.                                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NType == N \in Nat \ {0}

VARIABLES pc,    \* local control state of each process
          rcvd,  \* set of messages received by each process
          sent,  \* set of messages sent so far
          fd     \* fd[i] = TRUE iff the failure detector of i suspects someone

vars == << pc, rcvd, sent, fd >>

Proc  == 1 .. N
Votes == { "YES", "NO" }
Msg   == Proc \X Votes

Status == { "YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH" }

(***************************************************************************)
(* Helper operators                                                        *)
(***************************************************************************)
RcvdYes(i) == Cardinality({ m \in rcvd[i] : m[2] = "YES" })
RcvdNo(i)  == Cardinality({ m \in rcvd[i] : m[2] = "NO" })

Alive(i) == pc[i] # "CRASH"
Decided(i) == pc[i] \in { "COMMIT", "ABORT" }

(***************************************************************************)
(* Initial conditions                                                      *)
(***************************************************************************)
Init ==
  /\ pc \in [ Proc -> { "YES", "NO" } ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd = [ i \in Proc |-> FALSE ]

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

(***************************************************************************)
(* Process actions                                                         *)
(***************************************************************************)

\* A process crashes.
Crash(i) ==
  /\ Alive(i)
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << rcvd, sent, fd >>

\* A process broadcasts its YES vote.
SendYes(i) ==
  /\ pc[i] = "YES"
  /\ sent' = sent \cup { << i, "YES" >> }
  /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
  /\ UNCHANGED << rcvd, fd >>

\* A process broadcasts its NO vote.
SendNo(i) ==
  /\ pc[i] = "NO"
  /\ sent' = sent \cup { << i, "NO" >> }
  /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
  /\ UNCHANGED << rcvd, fd >>

\* A process receives a message that was sent but not yet received.
Receive(i) ==
  /\ Alive(i)
  /\ ~Decided(i)
  /\ \E m \in sent \ rcvd[i] :
        rcvd' = [ rcvd EXCEPT ![i] = rcvd[i] \cup { m } ]
  /\ UNCHANGED << pc, sent, fd >>

\* The failure detector of process i starts suspecting some process.
\* Suspicions only arise once some process has actually crashed.
Suspect(i) ==
  /\ Alive(i)
  /\ ~fd[i]
  /\ \E j \in Proc : pc[j] = "CRASH"
  /\ fd' = [ fd EXCEPT ![i] = TRUE ]
  /\ UNCHANGED << pc, rcvd, sent >>

\* Having sent its vote and received a NO, a process aborts.
UponNo(i) ==
  /\ pc[i] = "SENT"
  /\ RcvdNo(i) >= 1
  /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
  /\ UNCHANGED << rcvd, sent, fd >>

\* Having sent its vote and received YES from all processes, it commits.
UponYes(i) ==
  /\ pc[i] = "SENT"
  /\ RcvdNo(i) = 0
  /\ RcvdYes(i) >= N
  /\ pc' = [ pc EXCEPT ![i] = "COMMIT" ]
  /\ UNCHANGED << rcvd, sent, fd >>

\* Having sent its vote, suspecting a failure, and lacking all YES votes,
\* a process aborts.
UponSuspect(i) ==
  /\ pc[i] = "SENT"
  /\ fd[i]
  /\ RcvdYes(i) < N
  /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
  /\ UNCHANGED << rcvd, sent, fd >>

\* Non-stuttering, non-crash steps of a process.
Step(i) ==
  \/ SendYes(i)
  \/ SendNo(i)
  \/ Receive(i)
  \/ Suspect(i)
  \/ UponNo(i)
  \/ UponYes(i)
  \/ UponSuspect(i)

Next ==
  \/ \E i \in Proc : Step(i)
  \/ \E i \in Proc : Crash(i)
  \/ UNCHANGED vars

Fairness == \A i \in Proc : WF_vars(Step(i))

Spec        == Init        /\ [][Next]_vars /\ Fairness
SpecAllYes  == InitAllYes  /\ [][Next]_vars /\ Fairness
SpecAllNo   == InitAllNo   /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ pc \in [ Proc -> Status ]
  /\ sent \subseteq Msg
  /\ rcvd \in [ Proc -> SUBSET Msg ]
  /\ \A i \in Proc : rcvd[i] \subseteq sent
  /\ fd \in [ Proc -> BOOLEAN ]

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* No two processes decide differently.
Agreement ==
  [](\A i, j \in Proc : ~(pc[i] = "COMMIT" /\ pc[j] = "ABORT"))

\* If some process initially votes NO, no process ever commits.
AbortValidity ==
  (\E i \in Proc : pc[i] = "NO") => [](\A i \in Proc : pc[i] # "COMMIT")

\* If all processes vote YES and there is no failure and no suspicion,
\* then no process ever aborts.
CommitValidity ==
  ((\A i \in Proc : pc[i] = "YES")
     /\ [](\A i \in Proc : pc[i] # "CRASH" /\ ~fd[i]))
    => [](\A i \in Proc : pc[i] # "ABORT")

\* Every correct process eventually decides.
Termination ==
  <>(\A i \in Proc : pc[i] \in { "COMMIT", "ABORT", "CRASH" })

\* If all processes vote YES and no process ever crashes, then eventually
\* all processes commit.
EventualCommit ==
  ((\A i \in Proc : pc[i] = "YES")
     /\ [](\A i \in Proc : pc[i] # "CRASH"))
    => <>(\A i \in Proc : pc[i] = "COMMIT")

=============================================================================