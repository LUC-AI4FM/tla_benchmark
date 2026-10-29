---------------------------- MODULE MCInnerSerial ----------------------------
EXTENDS InnerSerial

CONSTANT MaxQLen

ASSUME MaxQLen \in Nat

MCNat == 0..MaxQLen

Constraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen

MCInitMem == [a \in Adr |-> CHOOSE v \in Val : TRUE]

MCInit == Init

MCNext == Next

MCSpec == Spec

AlwaysResponds ==
  /\ \A p \in Proc, r \in Reg :
        (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")
  /\ \A oi \in [proc : Proc, idx : MCNat] :
        (oi \in opId) ~> ((oi \in opId) => (opIdQ(oi).reg = "Done"))

=============================================================================