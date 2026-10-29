---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Integers, Sequences

CONSTANTS Data, MaxQLen

ASSUME /\ Data # {}
       /\ MaxQLen \in Nat \ {0}

VARIABLES AVar, BVar, AtoB, BtoA, queue

vars == <<AVar, BVar, AtoB, BtoA, queue>>

Bits == {0, 1}

-----------------------------------------------------------------------------
TypeOK ==
  /\ AVar \in Data \X Bits
  /\ BVar \in Data \X Bits
  /\ AtoB \in Seq(Data \X Bits)
  /\ BtoA \in Seq(Bits)
  /\ queue \in Seq(Data)
  /\ Len(queue) <= MaxQLen

RemoveAt(s, i) ==
  [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

-----------------------------------------------------------------------------
Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>
  /\ queue = << >>

(* Sender: repeatedly send its current value on AtoB *)
ASendData ==
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA, queue>>

(* Sender: receive an acknowledgment bit from BtoA *)
ARcvAck ==
  /\ BtoA # << >>
  /\ BtoA' = Tail(BtoA)
  /\ UNCHANGED <<AVar, BVar, AtoB, queue>>

(* Receiver: repeatedly send an acknowledgment of its current bit *)
BSendAck ==
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB, queue>>

(* Receiver: receive a data message; accept it if its bit is new *)
BRcvData ==
  /\ AtoB # << >>
  /\ IF Head(AtoB)[2] # BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE UNCHANGED BVar
  /\ AtoB' = Tail(AtoB)
  /\ UNCHANGED <<AVar, BtoA, queue>>

(* Lossy channels: nondeterministically drop a message *)
LoseMsgAtoB ==
  /\ AtoB # << >>
  /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(AtoB, i)
  /\ UNCHANGED <<AVar, BVar, BtoA, queue>>

LoseMsgBtoA ==
  /\ BtoA # << >>
  /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(BtoA, i)
  /\ UNCHANGED <<AVar, BVar, AtoB, queue>>

LoseMsg == LoseMsgAtoB \/ LoseMsgBtoA

(* Environment: produce a new pending data value *)
ProduceData ==
  /\ Len(queue) < MaxQLen
  /\ \E d \in Data : queue' = Append(queue, d)
  /\ UNCHANGED <<AVar, BVar, AtoB, BtoA>>

(* Inject new data into the sender when the endpoints agree *)
NewData ==
  /\ AVar = BVar
  /\ queue # << >>
  /\ AVar' = <<Head(queue), 1 - AVar[2]>>
  /\ queue' = Tail(queue)
  /\ UNCHANGED <<BVar, AtoB, BtoA>>

Next ==
  \/ ASendData
  \/ ARcvAck
  \/ BSendAck
  \/ BRcvData
  \/ LoseMsg
  \/ ProduceData
  \/ NewData

Fairness ==
  /\ WF_vars(ASendData)
  /\ WF_vars(BSendAck)
  /\ SF_vars(ARcvAck)
  /\ SF_vars(BRcvData)
  /\ WF_vars(NewData)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)
Inv ==
  /\ (AVar[2] = BVar[2]) => (AVar = BVar)
  /\ \A i \in 1..Len(AtoB) : (AtoB[i][2] = AVar[2]) => (AtoB[i] = AVar)
  /\ \A i \in 1..Len(AtoB) : (AtoB[i][2] # AVar[2]) => (AtoB[i] = BVar)

(* Liveness: the receiver eventually catches up with the sender *)
Liveness == (AVar # BVar) ~> (AVar = BVar)

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => Liveness
=============================================================================