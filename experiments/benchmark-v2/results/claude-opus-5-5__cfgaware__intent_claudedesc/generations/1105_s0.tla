---------------------------- MODULE nbacc_ray97 ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N >= 1

VARIABLES pc, rcvd, sent, fd

vars == << pc, rcvd, sent, fd >>

Proc == 1 .. N

Votes == {"YES", "NO"}

Status == {"YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH"}

Msgs == Proc \X Votes

TypeOK ==
  /\ pc \in [Proc -> Status]
  /\ sent \subseteq Msgs
  /\ rcvd \in [Proc -> SUBSET Msgs]
  /\ fd \in [Proc -> BOOLEAN]

(* Initialization scenarios *)
Init ==
  /\ pc \in [Proc -> Votes]
  /\ sent = {}
  /\ rcvd = [i \in Proc |-> {}]
  /\ fd \in [Proc -> {FALSE}]

InitAllYes ==
  /\ pc = [i \in Proc |-> "YES"]
  /\ sent = {}
  /\ rcvd = [i \in Proc |-> {}]
  /\ fd = [i \in Proc |-> FALSE]

InitAllNo ==
  /\ pc = [i \in Proc |-> "NO"]
  /\ sent = {}
  /\ rcvd = [i \in Proc |-> {}]
  /\ fd = [i \in Proc |-> FALSE]

(* A process may crash at any time *)
Crash(i) ==
  /\ pc[i] # "CRASH"
  /\ pc' = [pc EXCEPT ![i] = "CRASH"]
  /\ UNCHANGED << rcvd, sent, fd >>

(* Broadcast own vote *)
SendYes(i) ==
  /\ pc[i] = "YES"
  /\ sent' = sent \cup { << i, "YES" >> }
  /\ pc' = [pc EXCEPT ![i] = "SENT"]
  /\ UNCHANGED << rcvd, fd >>

SendNo(i) ==
  /\ pc[i] = "NO"
  /\ sent' = sent \cup { << i, "NO" >> }
  /\ pc' = [pc EXCEPT ![i] = "SENT"]
  /\ UNCHANGED << rcvd, fd >>

(* Receive a message that has been sent but not yet received *)
Receive(i) ==
  /\ pc[i] # "CRASH"
  /\ \E m \in sent \ rcvd[i] :
        rcvd' = [rcvd EXCEPT ![i] = rcvd[i] \cup {m}]
  /\ UNCHANGED << pc, sent, fd >>

(* Failure detector: may (possibly prematurely) suspect failures *)
UpdateFailureDetector(i) ==
  /\ pc[i] # "CRASH"
  /\ fd' \in { g \in [Proc -> BOOLEAN] :
                 \A j \in Proc \ {i} : g[j] = fd[j] }
  /\ fd' # fd
  /\ UNCHANGED << pc, rcvd, sent >>

HasNo(i) == \E j \in Proc : << j, "NO" >> \in rcvd[i]

AllYes(i) == \A j \in Proc : << j, "YES" >> \in rcvd[i]

Abort(i) ==
  /\ pc[i] = "SENT"
  /\ (fd[i] \/ HasNo(i))
  /\ pc' = [pc EXCEPT ![i] = "ABORT"]
  /\ UNCHANGED << rcvd, sent, fd >>

Commit(i) ==
  /\ pc[i] = "SENT"
  /\ ~fd[i]
  /\ ~HasNo(i)
  /\ AllYes(i)
  /\ pc' = [pc EXCEPT ![i] = "COMMIT"]
  /\ UNCHANGED << rcvd, sent, fd >>

NonCrashStep(i) ==
  \/ SendYes(i)
  \/ SendNo(i)
  \/ Receive(i)
  \/ Abort(i)
  \/ Commit(i)

Next ==
  \E i \in Proc :
     \/ Crash(i)
     \/ NonCrashStep(i)
     \/ UpdateFailureDetector(i)

Fairness == \A i \in Proc : WF_vars(NonCrashStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

SpecAllYes == InitAllYes /\ [][Next]_vars /\ Fairness

SpecAllNo == InitAllNo /\ [][Next]_vars /\ Fairness

(* Properties *)
AgrrLtl ==
  [](~(\E i \in Proc : pc[i] = "COMMIT") \/ ~(\E j \in Proc : pc[j] = "ABORT"))

AbortValidityLtl ==
  (\E i \in Proc : pc[i] = "NO") => [](\A i \in Proc : pc[i] # "COMMIT")

CommitValidityLtl ==
  ((\A i \in Proc : pc[i] = "YES") /\ [](\A i \in Proc : ~fd[i]))
     => [](\A i \in Proc : pc[i] # "ABORT")

TerminationLtl ==
  ([](\A i \in Proc : pc[i] # "CRASH") /\ [](\A i \in Proc : ~fd[i]))
     => <>(\A i \in Proc : pc[i] \in {"COMMIT", "ABORT"})

=============================================================================