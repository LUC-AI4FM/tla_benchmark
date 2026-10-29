--------------------------- MODULE MCAlternatingBit ---------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS Data, msgQLen, ackQLen

VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, rcvd

vars == <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

-----------------------------------------------------------------------------
(* Alternating bit protocol                                                *)
-----------------------------------------------------------------------------

ABInit == /\ msgQ = << >>
          /\ ackQ = << >>
          /\ sBit \in {0, 1}
          /\ sAck = sBit
          /\ rBit = sBit
          /\ sent \in Data
          /\ rcvd \in Data

ABTypeInv == /\ msgQ \in Seq({0, 1} \X Data)
             /\ ackQ \in Seq({0, 1})
             /\ sBit \in {0, 1}
             /\ sAck \in {0, 1}
             /\ rBit \in {0, 1}
             /\ sent \in Data
             /\ rcvd \in Data

SndNewValue(d) == /\ sAck = sBit
                  /\ sent' = d
                  /\ sBit' = 1 - sBit
                  /\ msgQ' = Append(msgQ, <<sBit', d>>)
                  /\ UNCHANGED <<ackQ, sAck, rBit, rcvd>>

ReSndMsg == /\ sAck # sBit
            /\ msgQ' = Append(msgQ, <<sBit, sent>>)
            /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

RcvMsg == /\ msgQ # << >>
          /\ msgQ' = Tail(msgQ)
          /\ rBit' = Head(msgQ)[1]
          /\ rcvd' = Head(msgQ)[2]
          /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

SndAck == /\ ackQ' = Append(ackQ, rBit)
          /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

RcvAck == /\ ackQ # << >>
          /\ ackQ' = Tail(ackQ)
          /\ sAck' = Head(ackQ)
          /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd>>

RemoveAt(q, i) == [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]

LoseMsg == /\ msgQ # << >>
           /\ \E i \in 1..Len(msgQ) : msgQ' = RemoveAt(msgQ, i)
           /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

LoseAck == /\ ackQ # << >>
           /\ \E i \in 1..Len(ackQ) : ackQ' = RemoveAt(ackQ, i)
           /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

ABNext == \/ \E d \in Data : SndNewValue(d)
          \/ ReSndMsg
          \/ RcvMsg
          \/ SndAck
          \/ RcvAck
          \/ LoseMsg
          \/ LoseAck

ABSpec == ABInit /\ [][ABNext]_vars

ABFairness == /\ WF_vars(ReSndMsg)
              /\ WF_vars(SndAck)
              /\ SF_vars(RcvMsg)
              /\ SF_vars(RcvAck)

-----------------------------------------------------------------------------
(* Model-checking harness                                                  *)
-----------------------------------------------------------------------------

SeqConstraint == /\ Len(msgQ) \leq msgQLen
                 /\ Len(ackQ) \leq ackQLen

ABCSpec == ABSpec /\ ABFairness

SentLeadsToRcvd == \A d \in Data : (sent = d) /\ (sBit # sAck) ~> (rcvd = d)

(* Possible permanent disagreement of the protocol bits (expected to be    *)
(* violated under fairness, i.e. its negation should hold).                *)
BitsEventuallyDisagreeForever == <>[](sBit # sAck)
BitsAgreeInfinitelyOften == []<>(sBit = sAck)

(* Derived action-temporal formula *)
ImpliedAction == [][ (sBit # sBit') => (sAck = sBit) ]_vars

(* Simple stability property over sent data *)
SentStable == [][ (sAck # sBit) => (sent' = sent) ]_vars

(* Concrete counterexample / postcondition structure in TLC trace style *)
TraceState == [msgQ |-> msgQ, ackQ |-> ackQ, sBit |-> sBit,
               sAck |-> sAck, rBit |-> rBit, sent |-> sent, rcvd |-> rcvd]

PostCondition == (sBit = sAck) => (Len(msgQ) \leq msgQLen)

=============================================================================