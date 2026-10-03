------------------------------ MODULE Bakery ------------------------------

EXTENDS Naturals, Integers

CONSTANTS NumProcs, MaxTicket

VARIABLES pc, choosing, number

Procs == 1..NumProcs

vars == << pc, choosing, number >>

TypeOK ==
  /\ pc \in [Procs -> {"choose1", "choose2", "choose3", "wait", "cs"}]
  /\ choosing \in [Procs -> BOOLEAN]
  /\ number \in [Procs -> 0..MaxTicket]

MaxNum ==
  LET S == { number[k] : k \in Procs } \cup {0} IN
    CHOOSE m \in S : \A n \in S : n <= m

NextTicket ==
  IF MaxNum + 1 <= MaxTicket THEN MaxNum + 1 ELSE MaxTicket

Before(i, j) ==
  \/ number[i] < number[j]
  \/ (number[i] = number[j] /\ i < j)

CanEnter(i) ==
  \A j \in Procs :
    (j = i) \/ (~choosing[j] /\ (number[j] = 0 \/ Before(i, j)))

Init ==
  /\ pc = [i \in Procs |-> "choose1"]
  /\ choosing = [i \in Procs |-> FALSE]
  /\ number = [i \in Procs |-> 0]

Choose1(i) ==
  /\ i \in Procs
  /\ pc[i] = "choose1"
  /\ pc' = [pc EXCEPT ![i] = "choose2"]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED number

Choose2(i) ==
  /\ i \in Procs
  /\ pc[i] = "choose2"
  /\ pc' = [pc EXCEPT ![i] = "choose3"]
  /\ number' = [number EXCEPT ![i] = NextTicket]
  /\ UNCHANGED choosing

Choose3(i) ==
  /\ i \in Procs
  /\ pc[i] = "choose3"
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED number

EnterCS(i) ==
  /\ i \in Procs
  /\ pc[i] = "wait"
  /\ CanEnter(i)
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << choosing, number >>

ExitCS(i) ==
  /\ i \in Procs
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "choose1"]
  /\ number' = [number EXCEPT ![i] = 0]
  /\ UNCHANGED choosing

Proc(i) == Choose1(i) \/ Choose2(i) \/ Choose3(i) \/ EnterCS(i) \/ ExitCS(i)

Next == \E i \in Procs : Proc(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Procs : WF_vars(Proc(i))

Mutex ==
  \A i, j \in Procs : (i # j) => ~(/\ pc[i] = "cs" /\ pc[j] = "cs")

Invariant ==
  /\ TypeOK
  /\ Mutex

=================================