------------------------------- MODULE Bakery -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ NumProcs >= 1
ASSUME MaxNum \in Nat

Proc == 1..NumProcs

VARIABLES num, choosing, pc, read, max, nxt

vars == << num, choosing, pc, read, max, nxt >>

Labels == {"loop", "d1", "d2", "d3", "w1", "w2", "cs"}

TypeOK ==
    /\ num \in [Proc -> Nat]
    /\ choosing \in [Proc -> BOOLEAN]
    /\ pc \in [Proc -> Labels]
    /\ read \in [Proc -> SUBSET Proc]
    /\ max \in [Proc -> Nat]
    /\ nxt \in [Proc -> Proc]

Init ==
    /\ num = [i \in Proc |-> 0]
    /\ choosing = [i \in Proc |-> FALSE]
    /\ read = [i \in Proc |-> {}]
    /\ max = [i \in Proc |-> 0]
    /\ nxt = [i \in Proc |-> 1]
    /\ pc = [i \in Proc |-> "loop"]

\* Start the choosing phase: raise the choosing flag and prepare the scan.
loop(self) ==
    /\ pc[self] = "loop"
    /\ choosing' = [choosing EXCEPT ![self] = TRUE]
    /\ read' = [read EXCEPT ![self] = {self}]
    /\ max' = [max EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "d1"]
    /\ UNCHANGED << num, nxt >>

\* Scan the tickets of all other processes to compute the maximum.
d1(self) ==
    /\ pc[self] = "d1"
    /\ IF read[self] # Proc
         THEN /\ \E j \in Proc \ read[self] :
                   /\ max' = [max EXCEPT ![self] =
                                IF num[j] > max[self] THEN num[j] ELSE max[self]]
                   /\ read' = [read EXCEPT ![self] = read[self] \cup {j}]
              /\ pc' = [pc EXCEPT ![self] = "d1"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "d2"]
              /\ UNCHANGED << max, read >>
    /\ UNCHANGED << num, choosing, nxt >>

\* Take ticket max + 1.
d2(self) ==
    /\ pc[self] = "d2"
    /\ num' = [num EXCEPT ![self] = max[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "d3"]
    /\ UNCHANGED << choosing, read, max, nxt >>

\* Clear the choosing flag and prepare for the waiting phase.
d3(self) ==
    /\ pc[self] = "d3"
    /\ choosing' = [choosing EXCEPT ![self] = FALSE]
    /\ read' = [read EXCEPT ![self] = {self}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, max, nxt >>

\* Pick another unchecked process and wait until it is not choosing;
\* if all have been checked, enter the critical section.
w1(self) ==
    /\ pc[self] = "w1"
    /\ IF read[self] # Proc
         THEN /\ \E j \in Proc \ read[self] :
                   /\ ~choosing[j]
                   /\ nxt' = [nxt EXCEPT ![self] = j]
              /\ pc' = [pc EXCEPT ![self] = "w2"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED nxt
    /\ UNCHANGED << num, choosing, read, max >>

\* Wait until the selected process has no ticket or lower priority.
w2(self) ==
    /\ pc[self] = "w2"
    /\ LET j == nxt[self] IN
         /\ \/ num[j] = 0
            \/ num[j] > num[self]
            \/ (num[j] = num[self] /\ j > self)
         /\ read' = [read EXCEPT ![self] = read[self] \cup {j}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, choosing, max, nxt >>

\* Critical section; release ticket on exit.
cs(self) ==
    /\ pc[self] = "cs"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "loop"]
    /\ UNCHANGED << choosing, read, max, nxt >>

p(self) ==
    \/ loop(self) \/ d1(self) \/ d2(self) \/ d3(self)
    \/ w1(self) \/ w2(self) \/ cs(self)

Next == \E self \in Proc : p(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Mutual exclusion
Invariant ==
    \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* State constraint bounding ticket values
Constraint == \A i \in Proc : num[i] <= MaxNum

\* Predicates whose possible-state counts are tracked
InCS == \E i \in Proc : pc[i] = "cs"

ChooseNumber == \E i \in Proc : pc[i] \in {"d1", "d2", "d3"}

=============================================================================