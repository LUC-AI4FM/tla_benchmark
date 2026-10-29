---------------------------- MODULE nbacg_guer01 ----------------------------
(***************************************************************************)
(* Parameterized asynchronous non-blocking atomic commitment (NBAC) with   *)
(* failure detectors, after Guerraoui's "Non-blocking atomic commit in     *)
(* asynchronous distributed systems with failure detectors" (failure-      *)
(* sensitive agreement problems).                                          *)
(*                                                                         *)
(* Each process initially votes YES or NO, broadcasts its vote, receives   *)
(* the votes of others, and may crash at any time.  A failure detector     *)
(* module at each process may start suspecting once some process has       *)
(* crashed.  A process commits after receiving YES from all processes, and *)
(* aborts after receiving a NO vote or when its failure detector suspects. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES
    pc,     \* control state of each process
    rcvd,   \* messages received by each process
    sent,   \* set of all messages that have been sent
    fd      \* fd[i] = TRUE iff the failure detector at i suspects someone

vars == << pc, rcvd, sent, fd >>

Proc == 1 .. N

Votes == { "YES", "NO" }

Locations == { "YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH" }

Msgs == [ src : Proc, type : Votes ]

Decided == { "ABORT", "COMMIT" }

(***************************************************************************)
(* Helper operators                                                        *)
(***************************************************************************)
Crashed(i) == pc[i] = "CRASH"

SomeoneCrashed == \E j \in Proc : Crashed(j)

RcvdYesFrom(i) == { m.src : m \in { mm \in rcvd[i] : mm.type = "YES" } }

RcvdNo(i) == \E m \in rcvd[i] : m.type = "NO"

(***************************************************************************)
(* Initial conditions                                                      *)
(***************************************************************************)
Init ==
    /\ pc \in [ Proc -> Votes ]
    /\ rcvd = [ i \in Proc |-> {} ]
    /\ sent = {}
    /\ fd = [ i \in Proc |-> FALSE ]

\* Specialized initial condition: every process votes YES
InitAllYes ==
    /\ pc = [ i \in Proc |-> "YES" ]
    /\ rcvd = [ i \in Proc |-> {} ]
    /\ sent = {}
    /\ fd = [ i \in Proc |-> FALSE ]

\* Specialized initial condition: every process votes NO
InitAllNo ==
    /\ pc = [ i \in Proc |-> "NO" ]
    /\ rcvd = [ i \in Proc |-> {} ]
    /\ sent = {}
    /\ fd = [ i \in Proc |-> FALSE ]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* A process that has not crashed (and not decided) may crash at any time.
Crash(i) ==
    /\ pc[i] \notin { "CRASH" } \cup Decided
    /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
    /\ UNCHANGED << rcvd, sent, fd >>

\* A process broadcasts its vote.
Send(i) ==
    /\ pc[i] \in Votes
    /\ sent' = sent \cup { [ src |-> i, type |-> pc[i] ] }
    /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
    /\ UNCHANGED << rcvd, fd >>

\* A non-crashed process receives a message that has been sent.
Receive(i) ==
    /\ ~Crashed(i)
    /\ \E m \in sent \ rcvd[i] :
          rcvd' = [ rcvd EXCEPT ![i] = rcvd[i] \cup { m } ]
    /\ UNCHANGED << pc, sent, fd >>

\* The failure detector at a non-crashed process starts suspecting.
\* It may only do so if some process has actually crashed.
Suspect(i) ==
    /\ ~Crashed(i)
    /\ pc[i] \notin Decided
    /\ ~fd[i]
    /\ SomeoneCrashed
    /\ fd' = [ fd EXCEPT ![i] = TRUE ]
    /\ UNCHANGED << pc, rcvd, sent >>

\* Commit after receiving YES from all processes.
Commit(i) ==
    /\ pc[i] = "SENT"
    /\ RcvdYesFrom(i) = Proc
    /\ ~RcvdNo(i)
    /\ pc' = [ pc EXCEPT ![i] = "COMMIT" ]
    /\ UNCHANGED << rcvd, sent, fd >>

\* Abort after receiving a NO vote or upon suspicion.
Abort(i) ==
    /\ pc[i] = "SENT"
    /\ RcvdNo(i) \/ (fd[i] /\ RcvdYesFrom(i) # Proc)
    /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
    /\ UNCHANGED << rcvd, sent, fd >>

\* Non-stuttering actions of process i (excluding crashes)
ProcStep(i) ==
    \/ Send(i)
    \/ Receive(i)
    \/ Suspect(i)
    \/ Commit(i)
    \/ Abort(i)

Next ==
    \/ \E i \in Proc : Crash(i) \/ ProcStep(i)
    \/ UNCHANGED vars

Fairness == \A i \in Proc : WF_vars(ProcStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

SpecAllYes == InitAllYes /\ [][Next]_vars /\ Fairness

SpecAllNo == InitAllNo /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ pc \in [ Proc -> Locations ]
    /\ sent \subseteq Msgs
    /\ rcvd \in [ Proc -> SUBSET Msgs ]
    /\ \A i \in Proc : rcvd[i] \subseteq sent
    /\ fd \in [ Proc -> BOOLEAN ]

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* Agreement: no two processes decide differently.
Agreement ==
    [](\A i, j \in Proc : ~(pc[i] = "COMMIT" /\ pc[j] = "ABORT"))

\* Abort validity: if some process votes NO, no process ever commits.
AbortValidity ==
    (\E i \in Proc : pc[i] = "NO")
        => [](\A i \in Proc : pc[i] # "COMMIT")

\* Commit validity: if all vote YES and no process ever crashes,
\* then no process ever aborts.
CommitValidity ==
    ((\A i \in Proc : pc[i] = "YES") /\ [](\A i \in Proc : pc[i] # "CRASH"))
        => [](\A i \in Proc : pc[i] # "ABORT")

\* Termination: every correct process eventually decides.
Termination ==
    <>(\A i \in Proc : pc[i] \in Decided \cup { "CRASH" })

\* Eventual commit: if all vote YES and no failure occurs,
\* all processes eventually commit.
EventualCommit ==
    ((\A i \in Proc : pc[i] = "YES") /\ [](\A i \in Proc : pc[i] # "CRASH"))
        => <>(\A i \in Proc : pc[i] = "COMMIT")

=============================================================================