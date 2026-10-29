------------------------------ MODULE MCAlternatingBit ------------------------------
(***************************************************************************)
(* Model-checking harness for the alternating-bit protocol.                *)
(* The protocol itself lives in module AlternatingBit (given below as a    *)
(* submodule so the file is self-contained) and is imported via INSTANCE.  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC

    ---------------------------- MODULE AlternatingBit ----------------------------
    EXTENDS Naturals, Sequences

    CONSTANT Data

    VARIABLES msgQ,  \* sender -> receiver channel: <<bit, data>> messages
              ackQ,  \* receiver -> sender channel: bits
              sBit,  \* sender's current bit
              sAck,  \* last acknowledgement bit received by the sender
              rBit,  \* receiver's current bit
              sent,  \* last value sent
              rcvd   \* last value received

    vars == <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

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

    Lose(c) ==
        /\ c # << >>
        /\ \E i \in 1..Len(c) :
              c' = [j \in 1..(Len(c) - 1) |-> IF j < i THEN c[j] ELSE c[j + 1]]

    LoseMsg == Lose(msgQ) /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

    LoseAck == Lose(ackQ) /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

    ABNext ==
        \/ \E d \in Data : SndNewValue(d)
        \/ ReSndMsg
        \/ RcvMsg
        \/ SndAck
        \/ RcvAck
        \/ LoseMsg
        \/ LoseAck

    ABFairness ==
        /\ WF_vars(ReSndMsg)
        /\ WF_vars(SndAck)
        /\ SF_vars(RcvMsg)
        /\ SF_vars(RcvAck)

    ABSpec == ABInit /\ [][ABNext]_vars
    ===============================================================================