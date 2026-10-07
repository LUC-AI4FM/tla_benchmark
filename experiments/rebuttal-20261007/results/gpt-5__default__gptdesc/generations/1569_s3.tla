----------------------------- MODULE Bakery -----------------------------
EXTENDS Naturals

CONSTANTS Proc, TicketBound

ASSUME Proc # {}
ASSUME TicketBound \in Nat

VARIABLES
  pc,         \* control locations per process
  choosing,   \* [Proc -> BOOLEAN]
  number,     \* [Proc -> Nat]
  read,       \* [Proc -> SUBSET Proc], set of processes already examined in the waiting loop
  maxN,       \* [Proc -> Nat], local maximum ticket observed (+1) before taking a number
  next        \* [Proc -> Proc], the next process to examine in the waiting loop

PCVals ==
  {"start", "choosePick", "chooseSetNum", "chooseDone",
   "waitPick", "waitSpin1", "waitSpin2", "crit", "exit"}

TypeOK ==
  /\ pc \in [Proc -> PCVals]
  /\ choosing \in [Proc -> BOOLEAN]
  /\ number \in [Proc -> Nat]
  /\ read \in [Proc -> SUBSET Proc]
  /\ maxN \in [Proc -> Nat]
  /\ next \in [Proc -> Proc]

Max(S) ==
  IF S = {} THEN 0
  ELSE CHOOSE m \in S : \A n \in S : n <= m

LexLess(p, q) ==
  /\ p[1] < q[1]
  \/ (p[1] = q[1] /\ p[2] < q[2])

Init ==
  /\ pc = [i \in Proc |-> "start"]
  /\ choosing = [i \in Proc |-> FALSE]
  /\ number = [i \in Proc |-> 0]
  /\ read = [i \in Proc |-> {}]
  /\ maxN = [i \in Proc |-> 0]
  /\ \E a \in Proc :
        next = [i \in Proc |-> a]

ProcStep(i) ==
  \/ /\ pc[i] = "start"
     /\ choosing' = [choosing EXCEPT ![i] = TRUE]
     /\ read' = [read EXCEPT ![i] = {}]
     /\ pc' = [pc EXCEPT ![i] = "choosePick"]
     /\ UNCHANGED << number, maxN, next >>

  \/ /\ pc[i] = "choosePick"
     /\ maxN' = [maxN EXCEPT ![i] = Max({ number[p] : p \in Proc }) + 1]
     /\ pc' = [pc EXCEPT ![i] = "chooseSetNum"]
     /\ UNCHANGED << choosing, number, read, next >>

  \/ /\ pc[i] = "chooseSetNum"
     /\ number' = [number EXCEPT ![i] = maxN[i]]
     /\ pc' = [pc EXCEPT ![i] = "chooseDone"]
     /\ UNCHANGED << choosing, read, maxN, next >>

  \/ /\ pc[i] = "chooseDone"
     /\ choosing' = [choosing EXCEPT ![i] = FALSE]
     /\ pc' = [pc EXCEPT ![i] = "waitPick"]
     /\ UNCHANGED << number, read, maxN, next >>

  \/ /\ pc[i] = "waitPick"
     /\ read[i] = Proc \ {i}
     /\ pc' = [pc EXCEPT ![i] = "crit"]
     /\ UNCHANGED << choosing, number, read, maxN, next >>

  \/ /\ pc[i] = "waitPick"
     /\ \E j \in Proc \ {i} : j \notin read[i]
     /\ \E j \in Proc \ {i} :
           /\ j \notin read[i]
           /\ next' = [next EXCEPT ![i] = j]
           /\ pc' = [pc EXCEPT ![i] = "waitSpin1"]
     /\ UNCHANGED << choosing, number, read, maxN >>

  \/ /\ pc[i] = "waitSpin1"
     /\ ~choosing[next[i]]
     /\ pc' = [pc EXCEPT ![i] = "waitSpin2"]
     /\ UNCHANGED << choosing, number, read, maxN, next >>

  \/ /\ pc[i] = "waitSpin2"
     /\ number[next[i]] = 0
        \/ ~LexLess(<< number[next[i]], next[i] >>, << number[i], i >>)
     /\ read' = [read EXCEPT ![i] = read[i] \cup { next[i] }]
     /\ pc' = [pc EXCEPT ![i] = "waitPick"]
     /\ UNCHANGED << choosing, number, maxN, next >>

  \/ /\ pc[i] = "crit"
     /\ pc' = [pc EXCEPT ![i] = "exit"]
     /\ UNCHANGED << choosing, number, read, maxN, next >>

  \/ /\ pc[i] = "exit"
     /\ number' = [number EXCEPT ![i] = 0]
     /\ pc' = [pc EXCEPT ![i] = "start"]
     /\ UNCHANGED << choosing, read, maxN, next >>

Next ==
  \E i \in Proc : ProcStep(i)

vars == << pc, choosing, number, read, maxN, next >>

Spec ==
  Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in Proc : i # j => ~(pc[i] = "crit" /\ pc[j] = "crit")

StateConstraint ==
  Max({ number[p] : p \in Proc }) <= TicketBound
=============================================================================