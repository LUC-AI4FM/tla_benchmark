---- MODULE Bakery ----
EXTENDS Naturals

CONSTANTS NumProcs, MaxTicket

ASSUME /\ NumProcs \in Nat \ {0}
       /\ MaxTicket \in Nat \ {0}

Proc == 1..NumProcs

VARIABLES choosing, number, inCS

vars == << choosing, number, inCS >>

Init ==
  /\ choosing = [i \in Proc |-> FALSE]
  /\ number   = [i \in Proc |-> 0]
  /\ inCS     = {}

TypeOK ==
  /\ choosing \in [Proc -> BOOLEAN]
  /\ number \in [Proc -> 0..MaxTicket]
  /\ inCS \subseteq Proc

Less(i, j) ==
  \/ number[i] < number[j]
  \/ /\ number[i] = number[j]
     /\ i < j

WaitForOthers(i) ==
  \A j \in Proc \ {i}:
    /\ ~choosing[j]
    /\ (number[j] = 0 \/ Less(i, j))

MaxOfNumbers(n) ==
  IF Proc = {} THEN 0
  ELSE
    CHOOSE m \in { n[p] : p \in Proc } :
      \A x \in { n[p] : p \in Proc } : m >= x

Try(i) ==
  /\ i \in Proc
  /\ number[i] = 0
  /\ ~choosing[i]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED << number, inCS >>

ChooseNum(i) ==
  /\ i \in Proc
  /\ choosing[i]
  /\ number[i] = 0
  /\ MaxOfNumbers(number) < MaxTicket
  /\ number' = [number EXCEPT ![i] = MaxOfNumbers(number) + 1]
  /\ UNCHANGED << choosing, inCS >>

ClearChoosing(i) ==
  /\ i \in Proc
  /\ choosing[i]
  /\ number[i] > 0
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED << number, inCS >>

EnterCS(i) ==
  /\ i \in Proc
  /\ ~choosing[i]
  /\ number[i] > 0
  /\ WaitForOthers(i)
  /\ i \notin inCS
  /\ inCS' = inCS \cup {i}
  /\ UNCHANGED << choosing, number >>

LeaveCS(i) ==
  /\ i \in Proc
  /\ i \in inCS
  /\ inCS' = inCS \ {i}
  /\ number' = [number EXCEPT ![i] = 0]
  /\ UNCHANGED choosing

Next ==
  \E i \in Proc :
      Try(i)
    \/ ChooseNum(i)
    \/ ClearChoosing(i)
    \/ EnterCS(i)
    \/ LeaveCS(i)

Spec ==
  Init /\ [][Next]_vars

Invariant ==
  \A i, j \in Proc : i # j => ~(i \in inCS /\ j \in inCS)
====