----------------------------- MODULE OneStepConsensus -----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, F, T

(*
  Processes, values, and distinguished markers
*)
Proc == 1..N
Values == {0, 1}
NoMsg == "NoMsg"
NoDecision == "NoDecision"

VARIABLES
  faulty,       \* subset of Proc: currently Byzantine processes
  InitCorrect,  \* subset of Proc: processes that are non-faulty initially; constant thereafter
  prop,         \* [Proc -> Values]: initial proposals
  state,        \* [Proc -> {"start","sent","receiving","decided","faulty"}]: per-process state
  broadcasted,  \* [Proc -> BOOLEAN]: whether a process has broadcast its proposal
  recvVal,      \* [Proc -> [Proc -> (Values \cup {NoMsg})]]: value received by i from j (or NoMsg)
  decidedVal    \* [Proc -> (Values \cup {NoDecision})]: per-process decision (or NoDecision)

vars == << faulty, InitCorrect, prop, state, broadcasted, recvVal, decidedVal >>

CurrCorrect == Proc \ faulty

(*
  Derived counters for sent and received messages
*)
SentCount(v) == Cardinality({ i \in Proc : broadcasted[i] /\ prop[i] = v })

RecvCount(i, v) == Cardinality({ j \in Proc : recvVal[i][j] = v })

TotalRecv(i) == RecvCount(i, 0) + RecvCount(i, 1)

(*
  Typing and basic bounds
*)
TypeOK ==
  /\ faulty \subseteq Proc
  /\ InitCorrect \subseteq Proc
  /\ prop \in [Proc -> Values]
  /\ state \in [Proc -> {"start","sent","receiving","decided","faulty"}]
  /\ broadcasted \in [Proc -> BOOLEAN]
  /\ recvVal \in [Proc -> [Proc -> (Values \cup {NoMsg})]]
  /\ decidedVal \in [Proc -> (Values \cup {NoDecision})]

FaultBoundInv == Cardinality(faulty) <= F

(*
  Initial states: two scenarios, all-0 or all-1 proposals
*)
InitCommon ==
  /\ faulty \subseteq Proc
  /\ Cardinality(faulty) <= F
  /\ broadcasted = [i \in Proc |-> FALSE]
  /\ recvVal = [i \in Proc |-> [j \in Proc |-> NoMsg]]
  /\ decidedVal = [i \in Proc |-> NoDecision]
  /\ state = [i \in Proc |-> IF i \in faulty THEN "faulty" ELSE "start"]
  /\ InitCorrect = Proc \ faulty

InitAll0 == InitCommon /\ prop = [i \in Proc |-> 0]
InitAll1 == InitCommon /\ prop = [i \in Proc |-> 1]

Init == InitAll0 \/ InitAll1

(*
  Actions
*)
Propose(i) ==
  /\ i \in Proc
  /\ i \notin faulty
  /\ state[i] = "start"
  /\ ~broadcasted[i]
  /\ broadcasted' = [broadcasted EXCEPT ![i] = TRUE]
  /\ state' = [state EXCEPT ![i] = "sent"]
  /\ UNCHANGED << faulty, InitCorrect, prop, recvVal, decidedVal >>

ProposeAct == \E i \in Proc : Propose(i)

ReceiveOne(i) ==
  \E j \in Proc, v \in Values :
    /\ i \in Proc
    /\ i \notin faulty
    /\ decidedVal[i] = NoDecision
    /\ recvVal[i][j] = NoMsg
    /\ ((j \in faulty) \/ (j \notin faulty /\ broadcasted[j]))
    /\ ((j \in faulty) \/ v = prop[j])
    /\ recvVal' = [recvVal EXCEPT ![i][j] = v]
    /\ state' = [state EXCEPT ![i] = IF state[i] = "start" THEN "receiving" ELSE @]
    /\ UNCHANGED << faulty, InitCorrect, prop, broadcasted, decidedVal >>

Decide(i) ==
  /\ i \in Proc
  /\ i \notin faulty
  /\ decidedVal[i] = NoDecision
  /\ LET c0 == RecvCount(i, 0)
         c1 == RecvCount(i, 1)
     IN /\ ((c0 >= T) \/ (c1 >= T))
        /\ ~((c0 >= T) /\ (c1 >= T))
        /\ decidedVal' = [decidedVal EXCEPT ![i] = IF c1 >= T THEN 1 ELSE 0]
        /\ state' = [state EXCEPT ![i] = "decided"]
        /\ UNCHANGED << faulty, InitCorrect, prop, broadcasted, recvVal >>

MainProc(i) == ReceiveOne(i) \/ Decide(i)

Main == \E i \in Proc : MainProc(i)

BecomeFaulty(i) ==
  /\ i \in Proc
  /\ i \notin faulty
  /\ Cardinality(faulty) < F
  /\ faulty' = faulty \cup {i}
  /\ state' = [state EXCEPT ![i] = "faulty"]
  /\ UNCHANGED << InitCorrect, prop, broadcasted, recvVal, decidedVal >>

BecomeFaultyAct == \E i \in Proc : BecomeFaulty(i)

Next == ProposeAct \/ Main \/ BecomeFaultyAct

(*
  Safety properties
*)
AgreementInv ==
  \A p \in InitCorrect :
    \A q \in InitCorrect :
      (decidedVal[p] \in Values /\ decidedVal[q] \in Values) => decidedVal[p] = decidedVal[q]

DecisionSoundnessInv ==
  /\ \A i \in Proc :
       decidedVal[i] = 1 => (RecvCount(i, 1) >= T /\ RecvCount(i, 0) < T)
  /\ \A i \in Proc :
       decidedVal[i] = 0 => (RecvCount(i, 0) >= T /\ RecvCount(i, 1) < T)

Safety == TypeOK /\ FaultBoundInv /\ AgreementInv /\ DecisionSoundnessInv

(*
  Liveness properties
  - Weak fairness on the main step (Receive/Decide)
  - Eventual decision or fault for initially correct processes
  - Validity under homogeneous initial proposals (all-0 or all-1 scenarios)
*)
TerminationWeak ==
  \A i \in InitCorrect : <> (decidedVal[i] \in Values \/ i \in faulty)

ValidityAll0 ==
  InitAll0 => [](\A i \in InitCorrect : decidedVal[i] \in {NoDecision, 0})

ValidityAll1 ==
  InitAll1 => [](\A i \in InitCorrect : decidedVal[i] \in {NoDecision, 1})

Spec == Init /\ [][Next]_vars /\ WF_vars(Main)

================================================================================