------------------------------ MODULE AlternatingBit ------------------------------

EXTENDS Naturals, TLC

CONSTANT Data

ASSUME Data # {}

VARIABLES sbit, rbit, abit, sdata, rdata

Bits == {0, 1}

vars == << sbit, rbit, abit, sdata, rdata >>

Init ==
  /\ sbit \in Bits
  /\ abit = sbit
  /\ rbit = sbit
  /\ sdata \in Data
  /\ rdata \in Data

Send ==
  /\ abit = sbit
  /\ sbit' = 1 - sbit
  /\ sdata' \in Data
  /\ UNCHANGED << rbit, rdata, abit >>

Recv ==
  /\ rbit # sbit
  /\ rbit' = sbit
  /\ rdata' = sdata
  /\ UNCHANGED << sbit, sdata, abit >>

Ack ==
  /\ rbit # abit
  /\ abit' = rbit
  /\ UNCHANGED << sbit, sdata, rbit, rdata >>

Next == Send \/ Recv \/ Ack

TypeInv ==
  /\ sbit \in Bits
  /\ rbit \in Bits
  /\ abit \in Bits
  /\ sdata \in Data
  /\ rdata \in Data

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Recv)
  /\ WF_vars(Ack)

SafetyProperty == []TypeInv

LivenessProperty == []<>(sbit # abit)

===============================================================================