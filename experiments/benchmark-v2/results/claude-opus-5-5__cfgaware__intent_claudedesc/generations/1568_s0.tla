---------------------------- MODULE Bakery ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ NumProcs >= 1
ASSUME MaxNum \in Nat /\ MaxNum >= 1

Procs == 1..NumProcs

VARIABLES num, choosing, pc, max, unchecked, nxt

vars == <<num, choosing, pc, max, unchecked, nxt>>

TypeOK ==
  /\ num \in [Procs -> Nat]
  /\ choosing \in [Procs -> BOOLEAN]
  /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}]
  /\ max \in [Procs -> Nat]
  /\ unchecked \in [Procs -> SUBSET Procs]
  /\ nxt \in [Procs -> Procs]

Init ==
  /\ num = [i \in Procs |-> 0]
  /\ choosing = [i \in Procs |-> FALSE]
  /\ pc = [i \in Procs |-> "ncs"]
  /\ max = [i \in Procs |-> 0]
  /\ unchecked = [i \in Procs |-> {}]
  /\ nxt = [i \in Procs |-> i]

\* Process i has priority over process j
Before(i, j) ==
  \/ num[j] = 0
  \/ num[i] < num[j]
  \/ (num[i] = num[j] /\ i < j)

InCS(i) == pc[i] = "cs"

NCS(i) ==
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "e1"]
  /\ UNCHANGED <<num, choosing, max, unchecked, nxt>>

\* Signal that the process is choosing a number
E1(i) ==
  /\ pc[i] = "e1"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ unchecked' = [unchecked EXCEPT ![i] = Procs \ {i}]
  /\ max' = [max EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "e2"]
  /\ UNCHANGED <<num, nxt>>

\* Scan other processes' numbers one at a time to find the maximum
E2(i) ==
  /\ pc[i] = "e2"
  /\ IF unchecked[i] # {}
       THEN \E j \in unchecked[i] :
              /\ unchecked' = [unchecked EXCEPT ![i] = unchecked[i] \ {j}]
              /\ max' = [max EXCEPT ![i] = IF num[j] > max[i] THEN num[j] ELSE max[i]]
              /\ UNCHANGED pc
       ELSE /\ pc' = [pc EXCEPT ![i] = "e3"]
            /\ UNCHANGED <<unchecked, max>>
  /\ UNCHANGED <<num, choosing, nxt>>

\* Set own number to one more than the maximum seen
ChooseNumber(i) ==
  /\ pc[i] = "e3"
  /\ num' = [num EXCEPT ![i] = max[i] + 1]
  /\ pc' = [pc EXCEPT ![i] = "e4"]
  /\ UNCHANGED <<choosing, max, unchecked, nxt>>

\* Clear the choosing flag and prepare to wait on all other processes
E4(i) ==
  /\ pc[i] = "e4"
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ unchecked' = [unchecked EXCEPT ![i] = Procs \ {i}]
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<num, max, nxt>>

\* Pick the next process to wait on, waiting for it to finish choosing
W1(i) ==
  /\ pc[i] = "w1"
  /\ IF unchecked[i] # {}
       THEN \E j \in unchecked[i] :
              /\ ~choosing[j]
              /\ nxt' = [nxt EXCEPT ![i] = j]
              /\ pc' = [pc EXCEPT ![i] = "w2"]
       ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
            /\ UNCHANGED nxt
  /\ UNCHANGED <<num, choosing, max, unchecked>>

\* Wait until this process has priority over process nxt[i]
W2(i) ==
  /\ pc[i] = "w2"
  /\ Before(i, nxt[i])
  /\ unchecked' = [unchecked EXCEPT ![i] = unchecked[i] \ {nxt[i]}]
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<num, choosing, max, nxt>>

\* Critical section (no-op)
CS(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED <<num, choosing, max, unchecked, nxt>>

Exit(i) ==
  /\ pc[i] = "exit"
  /\ num' = [num EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED <<choosing, max, unchecked, nxt>>

Proc(i) ==
  \/ NCS(i)
  \/ E1(i)
  \/ E2(i)
  \/ ChooseNumber(i)
  \/ E4(i)
  \/ W1(i)
  \/ W2(i)
  \/ CS(i)
  \/ Exit(i)

Next == \E i \in Procs : Proc(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Mutual exclusion: at most one process in the critical section
Invariant ==
  \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))

\* Bound ticket values for finite-state model checking
Constraint ==
  \A i \in Procs : num[i] <= MaxNum /\ max[i] <= MaxNum

\* Possible counts of processes simultaneously in the critical section
PossibleCounts == 0..NumProcs

_POSSIBLE ==
  Cardinality({i \in Procs : InCS(i)}) \in PossibleCounts

=============================================================================