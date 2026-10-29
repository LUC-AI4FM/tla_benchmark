------------------------------ MODULE nbacg_guer01 ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME NAssump == N \in Nat /\ N >= 1

VARIABLES pc,    \* local state of each process
          rcvd,  \* set of messages received by each process
          sent,  \* set of messages sent by all processes
          fd     \* fd[i] = TRUE iff the failure detector of i suspects some process

vars == << pc, rcvd, sent, fd >>

Proc     == 1 .. N
Votes    == { "YES", "NO" }
Messages == Proc \X Votes
Location == { "YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH" }

----------------------------------------------------------------------------
(* Helper operators *)

Crashed == { i \in Proc : pc[i] = "CRASH" }

RcvdYes(i) == { m \in rcvd[i] : m[2] = "YES" }
RcvdNo(i)  == { m \in rcvd[i] : m[2] = "NO" }

----------------------------------------------------------------------------
(* Initial conditions *)

Init ==
  /\ pc   \in [ Proc -> { "YES", "NO" } ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd   = [ i \in Proc |-> FALSE ]

InitAllYes ==
  /\ pc   = [ i \in Proc |-> "YES" ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd   = [ i \in Proc |-> FALSE ]

InitAllNo ==
  /\ pc   = [ i \in Proc |-> "NO" ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ fd   = [ i \in Proc |-> FALSE ]

----------------------------------------------------------------------------
(* Actions *)

\* A process that has not yet decided may crash.
Crash(i) ==
  /\ pc[i] \in { "YES", "NO", "SENT" }
  /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
  /\ UNCHANGED << rcvd, sent, fd >>

\* The failure detector of i starts suspecting once some process has crashed.
Suspect(i) ==
  /\ pc[i] \notin { "CRASH" }
  /\ fd[i] = FALSE
  /\ Crashed # {}
  /\ fd' = [ fd EXCEPT ![i] = TRUE ]
  /\ UNCHANGED << pc, rcvd, sent >>

\* A process receives some message that was sent but not yet received.
Receive(i) ==
  /\ pc[i] # "CRASH"
  /\ \E m \in sent \ rcvd[i] :
        rcvd' = [ rcvd EXCEPT ![i] = rcvd[i] \cup { m } ]
  /\ UNCHANGED << pc, sent, fd >>

\* A process broadcasts its vote YES.
SendYes(i) ==
  /\ pc[i] = "YES"
  /\ sent' = sent \cup { << i, "YES" >> }
  /\ pc'   = [ pc EXCEPT ![i] = "SENT" ]
  /\ UNCHANGED << rcvd, fd >>

\* A process broadcasts its vote NO.
SendNo(i) ==
  /\ pc[i] = "NO"
  /\ sent' = sent \cup { << i, "NO" >> }
  /\ pc'   = [ pc EXCEPT ![i] = "SENT" ]
  /\ UNCHANGED << rcvd, fd >>

\* Abort if a NO vote has been received or some process is suspected.
Abort(i) ==
  /\ pc[i] = "SENT"
  /\ RcvdNo(i) # {} \/ (fd[i] /\ Cardinality(RcvdYes(i)) < N)
  /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
  /\ UNCHANGED << rcvd, sent, fd >>

\* Commit if YES votes have been received from all processes.
Commit(i) ==
  /\ pc[i] = "SENT"
  /\ RcvdNo(i) = {}
  /\ Cardinality(RcvdYes(i)) = N
  /\ pc' = [ pc EXCEPT ![i] = "COMMIT" ]
  /\ UNCHANGED << rcvd, sent, fd >>

\* Non-stuttering process actions (subject to weak fairness).
Proc_Step(i) ==
  \/ Receive(i)
  \/ SendYes(i)
  \/ SendNo(i)
  \/ Suspect(i)
  \/ Abort(i)
  \/ Commit(i)

Next ==
  \/ \E i \in Proc : Crash(i) \/ Proc_Step(i)
  \/ UNCHANGED vars

Fairness == \A i \in Proc : WF_vars(Proc_Step(i))

Spec       == Init       /\ [][Next]_vars /\ Fairness
SpecAllYes == InitAllYes /\ [][Next]_vars /\ Fairness
SpecAllNo  == InitAllNo  /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
(* Invariants and properties *)

TypeOK ==
  /\ pc   \in [ Proc -> Location ]
  /\ sent \subseteq Messages
  /\ rcvd \in [ Proc -> SUBSET Messages ]
  /\ fd   \in [ Proc -> BOOLEAN ]

NoCrash == \A i \in Proc : pc[i] # "CRASH"

\* No two processes decide differently.
Agreement ==
  [] ~(\E i, j \in Proc : pc[i] = "ABORT" /\ pc[j] = "COMMIT")

\* If all processes vote YES and no process crashes, no process aborts.
AbortValidity ==
  ((\A i \in Proc : pc[i] = "YES") /\ []NoCrash)
     => [](\A i \in Proc : pc[i] # "ABORT")

\* If some process votes NO, no process commits.
CommitValidity ==
  (\E i \in Proc : pc[i] = "NO")
     => [](\A i \in Proc : pc[i] # "COMMIT")

\* Every correct process eventually decides.
Termination ==
  <>(\A i \in Proc : pc[i] \in { "ABORT", "COMMIT", "CRASH" })

\* If all vote YES and no process crashes, all eventually commit.
EventualCommit ==
  ((\A i \in Proc : pc[i] = "YES") /\ []NoCrash)
     => <>(\A i \in Proc : pc[i] = "COMMIT")

=============================================================================