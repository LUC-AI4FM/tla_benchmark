--------------------------- MODULE MCAlternatingBit ---------------------------
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(* The alternating-bit protocol specification that this harness imports.  *)
(* It is given here as a submodule so that this file is self-contained.   *)
(***************************************************************************)

-------------------------- MODULE AlternatingBit ------------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, rcvd

abvars == <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

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
  /\ msgQ' = Append(msgQ, <<sBit', d>>)
  /\ UNCHANGED <<ackQ, sAck, rBit, rcvd>>

ReSndMsg ==
  /\ sAck # sBit
  /\ msgQ' = Append(msgQ, <<sBit, sent>>)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

RcvMsg ==
  /\ msgQ # << >>
  /\ msgQ' = Tail(msgQ)
  /\ rBit' = Head(msgQ)[1]
  /\ rcvd' = Head(msgQ)[2]
  /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

SndAck ==
  /\ ackQ' = Append(ackQ, rBit)
  /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

RcvAck ==
  /\ ackQ # << >>
  /\ ackQ' = Tail(ackQ)
  /\ sAck' = Head(ackQ)
  /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd>>

Remove(i, q) == [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]

LoseMsg ==
  /\ msgQ # << >>
  /\ \E i \in 1..Len(msgQ) : msgQ' = Remove(i, msgQ)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

LoseAck ==
  /\ ackQ # << >>
  /\ \E i \in 1..Len(ackQ) : ackQ' = Remove(i, ackQ)
  /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

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
===============================================================================