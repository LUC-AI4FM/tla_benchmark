--------------------------- MODULE MCAlternatingBit ---------------------------
(***************************************************************************)
(* Model-checking harness around the alternating-bit protocol.  The       *)
(* protocol itself, which the original harness imports from another       *)
(* module, is written out in full here so that this module parses on its   *)
(* own.                                                                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC

CONSTANTS Data,       \* the set of data values that can be sent
          msgQLen,    \* bound on the length of the message queue
          ackQLen     \* bound on the length of the acknowledgement queue

ASSUME /\ Data # {}
       /\ msgQLen \in Nat
       /\ ackQLen \in Nat

VARIABLES msgQ,  \* sender -> receiver channel: sequence of <<bit, data>>
          ackQ,  \* receiver -> sender channel: sequence of bits
          sBit,  \* sender's current bit
          sAck,  \* last acknowledgement bit the sender received
          rBit,  \* last bit the receiver received
          sent,  \* last value the sender sent
          rcvd   \* last value the receiver received

abvars == << msgQ, ackQ, sBit, sAck, rBit, sent, rcvd >>
vars   == abvars

(***************************************************************************)
(* The alternating-bit protocol                                            *)
(***************************************************************************)
ABTypeInv ==
  /\ msgQ \in Seq({0, 1} \X Data)
  /\ ackQ \in Seq({0, 1})
  /\ sBit \in {0, 1}
  /\ sAck \in {0, 1}
  /\ rBit \in {0, 1}
  /\ sent \in Data
  /\ rcvd \in Data

ABInit ==
  /\ msgQ = << >>
  /\ ackQ = << >>
  /\ sBit \in {0, 1}
  /\ sAck = sBit
  /\ rBit = sBit
  /\ sent \in Data
  /\ rcvd \in Data

SndNewValue(d) ==
  /\ sAck = sBit
  /\ sent' = d
  /\ sBit' = 1 - sBit
  /\ msgQ' = Append(msgQ, << sBit', d >>)
  /\ UNCHANGED << ackQ, sAck, rBit, rcvd >>

ReSndMsg ==
  /\ sAck # sBit
  /\ msgQ' = Append(msgQ, << sBit, sent >>)
  /\ UNCHANGED << ackQ, sBit, sAck, rBit, sent, rcvd >>

RcvMsg ==
  /\ msgQ # << >>
  /\ msgQ' = Tail(msgQ)
  /\ rBit' = Head(msgQ)[1]
  /\ rcvd' = Head(msgQ)[2]
  /\ UNCHANGED << ackQ, sBit, sAck, sent >>

SndAck ==
  /\ ackQ' = Append(ackQ, rBit)
  /\ UNCHANGED << msgQ, sBit, sAck, rBit, sent, rcvd >>

RcvAck ==
  /\ ackQ # << >>
  /\ ackQ' = Tail(ackQ)
  /\ sAck' = Head(ackQ)
  /\ UNCHANGED << msgQ, sBit, rBit, sent, rcvd >>

Lose(q) ==
  /\ q # << >>
  /\ \E i \in 1..Len(q) :
        q' = [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]
  /\ UNCHANGED << sBit, sAck, rBit, sent, rcvd >>

LoseMsg == Lose(msgQ) /\ UNCHANGED ackQ
LoseAck == Lose(ackQ) /\ UNCHANGED msgQ

ABNext ==
  \/ \E d \in Data : SndNewValue(d)
  \/ ReSndMsg
  \/ RcvMsg
  \/ SndAck
  \/ RcvAck
  \/ LoseMsg
  \/ LoseAck

ABFairness ==
  /\ WF_abvars(ReSndMsg)
  /\ WF_abvars(SndAck)
  /\ SF_abvars(RcvMsg)
  /\ SF_abvars(RcvAck)

ABSpec == ABInit /\ [][ABNext]_abvars /\ ABFairness

(***************************************************************************)
(* Harness: initial predicate and next-state relation                      *)
(***************************************************************************)
Init == ABInit
Next == ABNext

(***************************************************************************)
(* Queue-length state constraint, which keeps the model finite             *)
(***************************************************************************)
SeqConstraint ==
  /\ Len(msgQ) \leq msgQLen
  /\ Len(ackQ) \leq ackQLen

(***************************************************************************)
(* Safety invariant                                                        *)
(***************************************************************************)
TypeOK == ABTypeInv

(***************************************************************************)
(* Liveness: a value that is sent and still unacknowledged is eventually   *)
(* received.                                                               *)
(***************************************************************************)
SentLeadsToRcvd ==
  \A d \in Data : (sent = d) /\ (sBit # sAck) ~> (rcvd = d)

(***************************************************************************)
(* Permanent disagreement of the protocol bits.                            *)
(*   PermanentDisagreement says that eventually the sender's bit and its   *)
(*   acknowledgement bit differ forever.                                   *)
(*   NoPermanentDisagreement is the property to check.  Under ABSpec       *)
(*   alone, without the added condition, TLC is expected to find a         *)
(*   counterexample to it.                                                 *)
(***************************************************************************)
PermanentDisagreement   == <>[](sBit # sAck)
NoPermanentDisagreement == []<>(sBit = sAck)

(***************************************************************************)
(* Derived action-temporal formula: the sender's bit changes only when the *)
(* previous value has been acknowledged, and a new value is sent with it.  *)
(***************************************************************************)
BitFlipOnlyWhenAcked ==
  [][(sBit' # sBit) => (sAck = sBit /\ msgQ' = Append(msgQ, << sBit', sent' >>))]_abvars

(***************************************************************************)
(* Stability of sent data: while the current value is unacknowledged,      *)
(* the value being sent does not change.                                   *)
(***************************************************************************)
SentStability ==
  [][(sBit # sAck) => (sent' = sent)]_abvars

(***************************************************************************)
(* Concrete counterexample structure, in the style of TLC trace data.      *)
(* It records a lasso trace in which messages are repeatedly lost, so      *)
(* sBit and sAck stay different forever.                                   *)
(***************************************************************************)
CEState(mq, aq, sb, sa, rb, s, r) ==
  [msgQ |-> mq, ackQ |-> aq, sBit |-> sb, sAck |-> sa,
   rBit |-> rb, sent |-> s, rcvd |-> r]

CounterExampleTrace ==
  LET d == CHOOSE v \in Data : TRUE
  IN  [ state  |-> { << 1, CEState(<< >>, << >>, 0, 0, 0, d, d) >>,
                     << 2, CEState(<< << 1, d >> >>, << >>, 1, 0, 0, d, d) >>,
                     << 3, CEState(<< >>, << >>, 1, 0, 0, d, d) >> },
        action |-> { << << 1, "SndNewValue" >>, "SndNewValue", << 2, "LoseMsg" >> >>,
                     << << 2, "LoseMsg" >>,     "LoseMsg",     << 3, "ReSndMsg" >> >>,
                     << << 3, "ReSndMsg" >>,    "ReSndMsg",    << 2, "LoseMsg" >> >> } ]

(***************************************************************************)
(* Postcondition that TLC evaluates after model checking.                  *)
(***************************************************************************)
PostCondition ==
  /\ TLCGet("level") \in Nat
  /\ DOMAIN CounterExampleTrace = {"state", "action"}
  /\ \A e \in CounterExampleTrace.action :
        /\ e[1][1] \in {s[1] : s \in CounterExampleTrace.state}
        /\ e[3][1] \in {s[1] : s \in CounterExampleTrace.state}

(***************************************************************************)
(* Combined specification: the protocol plus an added temporal condition.  *)
(* The added condition is that the acknowledgement channel is empty        *)
(* infinitely often.                                                       *)
(***************************************************************************)
AddedCondition == []<>(ackQ = << >>)

Spec == ABSpec /\ AddedCondition

THEOREM Spec => []TypeOK
=============================================================================