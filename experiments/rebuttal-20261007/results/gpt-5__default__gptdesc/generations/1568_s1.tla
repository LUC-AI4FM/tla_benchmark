------------------------------ MODULE Bakery ------------------------------

EXTENDS Naturals, TLC

CONSTANTS N, MaxTicket

ASSUME
  /\ N \in Nat /\ N >= 1
  /\ MaxTicket \in Nat /\ MaxTicket >= 1

Proc == 1..N

VARIABLES pc, choosing, number, j

vars == << pc, choosing, number, j >>

LexLess(i, k) == number[i] < number[k] \/ (number[i] = number[k] /\ i < k)

Init ==
  /\ pc = [i \in Proc |-> "start"]
  /\ choosing = [i \in Proc |-> FALSE]
  /\ number = [i \in Proc |-> 0]
  /\ j = [i \in Proc |-> 1]

StepStart(i) ==
  /\ i \in Proc
  /\ pc[i] = "start"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "setnum"]
  /\ UNCHANGED << number, j >>

StepSetNum(i) ==
  /\ i \in Proc
  /\ pc[i] = "setnum"
  /\ LET m == Max({ number[k] : k \in Proc })
     IN number' = [number EXCEPT ![i] = IF m + 1 <= MaxTicket THEN m + 1 ELSE MaxTicket]
  /\ pc' = [pc EXCEPT ![i] = "postchoose"]
  /\ UNCHANGED << choosing, j >>

StepPostChoose(i) ==
  /\ i \in Proc
  /\ pc[i] = "postchoose"
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED number

StepWaitSkipSelf(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait"
  /\ j[i] <= N
  /\ j[i] = i
  /\ j' = [j EXCEPT ![i] = j[i] + 1]
  /\ UNCHANGED << pc, choosing, number >>

StepWaitAdvance(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait"
  /\ j[i] <= N
  /\ j[i] # i
  /\ choosing[j[i]] = FALSE
  /\ number[j[i]] = 0 \/ ~LexLess(j[i], i)
  /\ j' = [j EXCEPT ![i] = j[i] + 1]
  /\ UNCHANGED << pc, choosing, number >>

StepWaitDone(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait"
  /\ j[i] = N + 1
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << choosing, number, j >>

StepCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << choosing, number, j >>

StepExit(i) ==
  /\ i \in Proc
  /\ pc[i] = "exit"
  /\ number' = [number EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "start"]
  /\ UNCHANGED << choosing, j >>

Step(i) ==
  StepStart(i)
  \/ StepSetNum(i)
  \/ StepPostChoose(i)
  \/ StepWaitSkipSelf(i)
  \/ StepWaitAdvance(i)
  \/ StepWaitDone(i)
  \/ StepCS(i)
  \/ StepExit(i)

Next == \E i \in Proc: Step(i)

Spec == Init /\ [][Next]_vars /\ \A i \in Proc: WF_vars(Step(i))

TypeOK ==
  /\ pc \in [Proc -> {"start", "setnum", "postchoose", "wait", "cs", "exit"}]
  /\ choosing \in [Proc -> BOOLEAN]
  /\ number \in [Proc -> 0..MaxTicket]
  /\ j \in [Proc -> 1..(N + 1)]

TicketBound == \A i \in Proc: number[i] \in 0..MaxTicket

MutualExclusion ==
  \A i, k \in Proc: i = k \/ ~(pc[i] = "cs" /\ pc[k] = "cs")

Inv == TypeOK /\ TicketBound /\ MutualExclusion

=============================================================================