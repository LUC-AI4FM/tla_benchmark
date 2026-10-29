------------------------------ MODULE NBACGuerraoui ------------------------------
(***************************************************************************)
(* Asynchronous non-blocking atomic commitment with failure detectors,     *)
(* following the algorithm in Guerraoui's work on failure-sensitive        *)
(* agreement problems.                                                      *)
(*                                                                         *)
(* Each process votes YES or NO and broadcasts its vote. A process that    *)
(* voted NO aborts immediately. A process that voted YES waits:            *)
(*   - it commits once it has received YES from every process;             *)
(*   - it aborts once it has received some NO;                             *)
(*   - it aborts once its failure detector suspects some process.          *)
(* Processes may crash at any time. The failure detector is accurate:      *)
(* it only suspects when some process has crashed. It is also complete:    *)
(* by fairness, a crash is eventually suspected.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

VARIABLES
  vote,     \* initial vote of each process (constant after Init)
  pc,       \* control location of each process
  crashed,  \* crashed[i] = TRUE iff process i has crashed
  fd,       \* fd[i] = TRUE iff i's failure detector suspects some process
  sent,     \* set of messages sent so far: <<sender, value>>
  rcvd      \* rcvd[i] = set of messages received by process i

vars == << vote, pc, crashed, fd, sent, rcvd >>

Proc     == 1 .. N
Vote     == { "YES", "NO" }
Location == { "YES", "NO", "WAIT", "COMMIT", "ABORT" }
Msg      == Proc \X Vote

---------------------------------------------------------------------------
(* Initial conditions *)

Init ==
  /\ vote \in [ Proc -> Vote ]
  /\ pc = vote
  /\ crashed = [ i \in Proc |-> FALSE ]
  /\ fd = [ i \in Proc |-> FALSE ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]

InitAllYes ==
  /\ vote = [ i \in Proc |-> "YES" ]
  /\ pc = vote
  /\ crashed = [ i \in Proc |-> FALSE ]
  /\ fd = [ i \in Proc |-> FALSE ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]

InitAllNo ==
  /\ vote = [ i \in Proc |-> "NO" ]
  /\ pc = vote
  /\ crashed = [ i \in Proc |-> FALSE ]
  /\ fd = [ i \in Proc |-> FALSE ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]

---------------------------------------------------------------------------
(* Process actions *)

\* A process crashes. It takes no further steps.
Crash(self) ==
  /\ ~crashed[self]
  /\ crashed' = [ crashed EXCEPT ![self] = TRUE ]
  /\ UNCHANGED << vote, pc, fd, sent, rcvd >>

\* A YES process broadcasts its vote and starts waiting.
SendYes(self) ==
  /\ ~crashed[self]
  /\ pc[self] = "YES"
  /\ sent' = sent \cup { << self, "YES" >> }
  /\ pc' = [ pc EXCEPT ![self] = "WAIT" ]
  /\ UNCHANGED << vote, crashed, fd, rcvd >>

\* A NO process broadcasts its vote and aborts.
SendNo(self) ==
  /\ ~crashed[self]
  /\ pc[self] = "NO"
  /\ sent' = sent \cup { << self, "NO" >> }
  /\ pc' = [ pc EXCEPT ![self] = "ABORT" ]
  /\ UNCHANGED << vote, crashed, fd, rcvd >>

\* A process receives a message that was sent and not yet received.
Receive(self) ==
  /\ ~crashed[self]
  /\ \E m \in sent \ rcvd[self] :
        rcvd' = [ rcvd EXCEPT ![self] = rcvd[self] \cup { m } ]
  /\ UNCHANGED << vote, pc, crashed, fd, sent >>

\* The failure detector of self starts suspecting (only if someone crashed).
Suspect(self) ==
  /\ ~crashed[self]
  /\ ~fd[self]
  /\ \E j \in Proc : j # self /\ crashed[j]
  /\ fd' = [ fd EXCEPT ![self] = TRUE ]
  /\ UNCHANGED << vote, pc, crashed, sent, rcvd >>

\* A waiting process commits after receiving YES from all processes.
Commit(self) ==
  /\ ~crashed[self]
  /\ pc[self] = "WAIT"
  /\ \A j \in Proc : << j, "YES" >> \in rcvd[self]
  /\ pc' = [ pc EXCEPT ![self] = "COMMIT" ]
  /\ UNCHANGED << vote, crashed, fd, sent, rcvd >>

\* A waiting process aborts after receiving some NO.
AbortOnNo(self) ==
  /\ ~crashed[self]
  /\ pc[self] = "WAIT"
  /\ \E j \in Proc : << j, "NO" >> \in rcvd[self]
  /\ pc' = [ pc EXCEPT ![self] = "ABORT" ]
  /\ UNCHANGED << vote, crashed, fd, sent, rcvd >>

\* A waiting process aborts when its failure detector suspects a process
\* and it has not yet received YES from everyone.
AbortOnSuspect(self) ==
  /\ ~crashed[self]
  /\ pc[self] = "WAIT"
  /\ fd[self]
  /\ ~(\A j \in Proc : << j, "YES" >> \in rcvd[self])
  /\ pc' = [ pc EXCEPT ![self] = "ABORT" ]
  /\ UNCHANGED << vote, crashed, fd, sent, rcvd >>

\* Non-stuttering, non-crash progress actions of a process.
Progress(self) ==
  \/ SendYes(self)
  \/ SendNo(self)
  \/ Receive(self)
  \/ Suspect(self)
  \/ Commit(self)
  \/ AbortOnNo(self)
  \/ AbortOnSuspect(self)

Step(self) ==
  \/ Progress(self)
  \/ Crash(self)

Next ==
  \/ \E self \in Proc : Step(self)
  \/ UNCHANGED vars

Fairness == \A self \in Proc : WF_vars(Progress(self))

Spec       == Init       /\ [][Next]_vars /\ Fairness
SpecAllYes == InitAllYes /\ [][Next]_vars /\ Fairness
SpecAllNo  == InitAllNo  /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Invariants and properties *)

TypeOK ==
  /\ vote \in [ Proc -> Vote ]
  /\ pc \in [ Proc -> Location ]
  /\ crashed \in [ Proc -> BOOLEAN ]
  /\ fd \in [ Proc -> BOOLEAN ]
  /\ sent \subseteq Msg
  /\ rcvd \in [ Proc -> SUBSET Msg ]
  /\ \A i \in Proc : rcvd[i] \subseteq sent

\* No two processes decide differently (uniform agreement).
Agreement ==
  [](\A i, j \in Proc : ~(pc[i] = "COMMIT" /\ pc[j] = "ABORT"))

\* Abort only if some process voted NO or some process crashed.
AbortValidity ==
  [](\A i \in Proc :
       pc[i] = "ABORT" =>
         (\E j \in Proc : vote[j] = "NO") \/ (\E j \in Proc : crashed[j]))

\* Commit only if all processes voted YES.
CommitValidity ==
  [](\A i \in Proc :
       pc[i] = "COMMIT" => (\A j \in Proc : vote[j] = "YES"))

\* Every correct process eventually decides.
Termination ==
  <>(\A i \in Proc : crashed[i] \/ pc[i] \in { "COMMIT", "ABORT" })

\* If all vote YES and no process ever crashes, all eventually commit.
EventualCommit ==
  ( (\A j \in Proc : vote[j] = "YES") /\ [](\A j \in Proc : ~crashed[j]) )
    => <>(\A i \in Proc : pc[i] = "COMMIT")

\* With all NO votes, nobody ever commits and all correct processes abort.
EventualAbortAllNo ==
  (\A j \in Proc : vote[j] = "NO")
    => <>(\A i \in Proc : crashed[i] \/ pc[i] = "ABORT")

=============================================================================