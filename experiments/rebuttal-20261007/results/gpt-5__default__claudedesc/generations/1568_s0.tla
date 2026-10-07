----------------------------- MODULE Bakery -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  NumProcs,
  MaxNum

ASSUME NumProcs \in Nat /\ NumProcs >= 1 /\ MaxNum \in Nat /\ MaxNum >= 1

Proc == 1..NumProcs
Labels == {"loop", "d1", "d2", "d3", "w1", "w2", "cs"}

VARIABLES
  num,              \* [Proc -> 0..MaxNum]
  choosing,         \* [Proc -> BOOLEAN]
  pc,               \* [Proc -> Labels]
  read,             \* [Proc -> 1..(NumProcs+1)]
  max,              \* [Proc -> 0..MaxNum]
  nxt,              \* [Proc -> 1..(NumProcs+1)]
  SeenInCS,         \* set of subsets of Proc seen for InCS
  SeenChooseNumber  \* set of subsets of Proc seen for ChooseNumber

vars == << num, choosing, pc, read, max, nxt, SeenInCS, SeenChooseNumber >>

InCSOf(p) == { i \in Proc : p[i] = "cs" }
ChooseNumberOf(p, c) == { i \in Proc : c[i] \/ p[i] \in {"d1","d2","d3"} }

InCS == InCSOf(pc)
ChooseNumber == ChooseNumberOf(pc, choosing)

TicketInc(m) == IF m < MaxNum THEN m + 1 ELSE MaxNum

OrderOK(i, j) ==
  (num[j] = 0) \/
  (num[j] > num[i]) \/
  (num[j] = num[i] /\ j > i)

Init ==
  /\ num = [i \in Proc |-> 0]
  /\ choosing = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "loop"]
  /\ read = [i \in Proc |-> 1]
  /\ max = [i \in Proc |-> 0]
  /\ nxt = [i \in Proc |-> 1]
  /\ SeenInCS = { InCS }
  /\ SeenChooseNumber = { ChooseNumber }

ActionLoop(i) ==
  /\ pc[i] = "loop"
  /\ num' = num
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "d1"]
  /\ read' = [read EXCEPT ![i] = 1]
  /\ max'  = [max  EXCEPT ![i] = 0]
  /\ nxt'  = nxt

ActionD1Cont(i) ==
  /\ pc[i] = "d1"
  /\ read[i] <= NumProcs
  /\ LET j == read[i] IN
       /\ num' = num
       /\ choosing' = choosing
       /\ max'  = [max  EXCEPT ![i] = IF max[i] < num[j] THEN num[j] ELSE max[i]]
       /\ read' = [read EXCEPT ![i] = read[i] + 1]
       /\ pc'   = [pc   EXCEPT ![i] =
                      IF read[i] + 1 <= NumProcs THEN "d1" ELSE "d2"]
       /\ nxt'  = nxt

ActionD2(i) ==
  /\ pc[i] = "d2"
  /\ num' = [num EXCEPT ![i] = TicketInc(max[i])]
  /\ choosing' = choosing
  /\ pc' = [pc EXCEPT ![i] = "d3"]
  /\ read' = read
  /\ max'  = max
  /\ nxt'  = nxt

ActionD3(i) ==
  /\ pc[i] = "d3"
  /\ num' = num
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ read' = read
  /\ max'  = max
  /\ nxt'  = [nxt EXCEPT ![i] = 1]

ActionW1ToW2(i) ==
  /\ pc[i] = "w1"
  /\ nxt[i] <= NumProcs
  /\ (nxt[i] = i \/ ~choosing[nxt[i]])
  /\ num' = num
  /\ choosing' = choosing
  /\ pc' = [pc EXCEPT ![i] = "w2"]
  /\ read' = read
  /\ max'  = max
  /\ nxt'  = nxt

ActionW1ToCS(i) ==
  /\ pc[i] = "w1"
  /\ nxt[i] > NumProcs
  /\ num' = num
  /\ choosing' = choosing
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ read' = read
  /\ max'  = max
  /\ nxt'  = nxt

ActionW2Self(i) ==
  /\ pc[i] = "w2"
  /\ nxt[i] <= NumProcs
  /\ nxt[i] = i
  /\ num' = num
  /\ choosing' = choosing
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ read' = read
  /\ max'  = max
  /\ nxt'  = [nxt EXCEPT ![i] = nxt[i] + 1]

ActionW2Advance(i) ==
  /\ pc[i] = "w2"
  /\ nxt[i] <= NumProcs
  /\ nxt[i] # i
  /\ OrderOK(i, nxt[i])
  /\ num' = num
  /\ choosing' = choosing
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ read' = read
  /\ max'  = max
  /\ nxt'  = [nxt EXCEPT ![i] = nxt[i] + 1]

ActionCSExit(i) ==
  /\ pc[i] = "cs"
  /\ num' = [num EXCEPT ![i] = 0]
  /\ choosing' = choosing
  /\ pc' = [pc EXCEPT ![i] = "loop"]
  /\ read' = read
  /\ max'  = max
  /\ nxt'  = nxt

ProcNext(i) ==
    ActionLoop(i)
  \/ ActionD1Cont(i)
  \/ ActionD2(i)
  \/ ActionD3(i)
  \/ ActionW1ToW2(i)
  \/ ActionW1ToCS(i)
  \/ ActionW2Self(i)
  \/ ActionW2Advance(i)
  \/ ActionCSExit(i)

Next ==
  /\ \E i \in Proc : ProcNext(i)
  /\ SeenInCS' = SeenInCS \cup { InCSOf(pc') }
  /\ SeenChooseNumber' = SeenChooseNumber \cup { ChooseNumberOf(pc', choosing') }

Spec == Init /\ [][Next]_vars

Invariant ==
  \A i, j \in Proc : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

Constraint ==
  \A i \in Proc : num[i] \in 0..MaxNum

PossibleCounts ==
  /\ Cardinality(SeenInCS) = 113
  /\ Cardinality(SeenChooseNumber) = 180

PostCondition == PossibleCounts

=============================================================================