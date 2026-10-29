------------------------------ MODULE HandshakeChannel ------------------------------
EXTENDS Naturals

CONSTANT Data

ASSUME DataNonEmpty == Data # {}

VARIABLES val, rdy, ack, lastStep

vars == << val, rdy, ack, lastStep >>

Steps == {"init", "send", "rcv"}

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack \in {0, 1}
    /\ lastStep \in Steps

Init ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack = rdy
    /\ lastStep = "init"

Send ==
    /\ rdy = ack
    /\ val' \in Data
    /\ rdy' = 1 - rdy
    /\ UNCHANGED ack
    /\ lastStep' = "send"

Rcv ==
    /\ rdy # ack
    /\ ack' = 1 - ack
    /\ UNCHANGED << val, rdy >>
    /\ lastStep' = "rcv"

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
Pending == rdy # ack

BitInvariant ==
    (rdy = ack) <=> (lastStep \in {"init", "rcv"})

Inv == TypeInvariant /\ BitInvariant

NoOverwrite ==
    [][ (val' # val \/ rdy' # rdy) => (rdy = ack) ]_vars

NoSpuriousAck ==
    [][ ack' # ack => (rdy # ack) ]_vars

ReliableSlot ==
    [][ \/ (~Pending /\ Pending' /\ val' \in Data /\ ack' = ack)
        \/ (Pending /\ ~Pending' /\ val' = val /\ rdy' = rdy) ]_vars

-----------------------------------------------------------------------------
LEMMA InitTypeOK == Init => TypeInvariant
  BY DEF Init, TypeInvariant, Steps

LEMMA SendPreservesType == TypeInvariant /\ Send => TypeInvariant'
  BY DEF TypeInvariant, Send, Steps

LEMMA RcvPreservesType == TypeInvariant /\ Rcv => TypeInvariant'
  BY DEF TypeInvariant, Rcv, Steps

LEMMA StutterPreservesType == TypeInvariant /\ UNCHANGED vars => TypeInvariant'
  BY DEF TypeInvariant, vars

LEMMA InitInv == Init => Inv
  BY DEF Init, Inv, TypeInvariant, BitInvariant, Steps

LEMMA NextPreservesInv == Inv /\ [Next]_vars => Inv'
  BY DEF Inv, TypeInvariant, BitInvariant, Next, Send, Rcv, vars, Steps

THEOREM TypeCorrect == Spec => []TypeInvariant

THEOREM BitPatternCorrect == Spec => []BitInvariant

THEOREM InvCorrect == Spec => []Inv

THEOREM NoOverwriteThm == Spec => NoOverwrite

THEOREM NoSpuriousAckThm == Spec => NoSpuriousAck

THEOREM ReliableSlotThm == Spec => ReliableSlot
=============================================================================