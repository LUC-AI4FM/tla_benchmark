------------------------------ MODULE AlternatingBit ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Data, MaxQ

ASSUME Data # {} /\ MaxQ \in Nat \ {0}

Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************
--algorithm AB {
  variables AVar \in Data \X {1}, BVar = AVar,
            AtoB = << >>, BtoA = << >>, q = << >>;

  fair process (SA = "SA") { sa: while (TRUE) { AtoB := Append(AtoB, AVar) } }
  fair+ process (RA = "RA") { ra: while (TRUE) { await BtoA # << >>; BtoA := Tail(BtoA) } }
  fair process (SB = "SB") { sb: while (TRUE) { BtoA := Append(BtoA, BVar[2]) } }
  fair+ process (RB = "RB") { rb: while (TRUE) { await AtoB # << >>;
                                   if (Head(AtoB)[2] # BVar[2]) { BVar := Head(AtoB) };
                                   AtoB := Tail(AtoB) } }
  process (LA = "LA") { la: while (TRUE) { await AtoB # << >>;
                          with (i \in 1..Len(AtoB)) { AtoB := Remove(i, AtoB) } } }
  process (LB = "LB") { lb: while (TRUE) { await BtoA # << >>;
                          with (i \in 1..Len(BtoA)) { BtoA := Remove(i, BtoA) } } }
  fair process (ND = "ND") { nd: while (TRUE) { await AVar = BVar /\ q # << >>;
                                 AVar := << Head(q), 1 - AVar[2] >>; q := Tail(q) } }
  process (PR = "PR") { pr: while (TRUE) { await Len(q) < MaxQ;
                          with (d \in Data) { q := Append(q, d) } } }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES AVar, BVar, AtoB, BtoA, q, pc

vars == << AVar, BVar, AtoB, BtoA, q, pc >>

ProcSet == {"SA", "RA", "SB", "RB", "LA", "LB", "ND", "PR"}

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>
        /\ q = << >>
        /\ pc = [self \in ProcSet |->
                   CASE self = "SA" -> "sa"
                     [] self = "RA" -> "ra"
                     [] self = "SB" -> "sb"
                     [] self = "RB" -> "rb"
                     [] self = "LA" -> "la"
                     [] self = "LB" -> "lb"
                     [] self = "ND" -> "nd"
                     [] self = "PR" -> "pr"]

sa == /\ pc["SA"] = "sa"
      /\ AtoB' = Append(AtoB, AVar)
      /\ pc' = [pc EXCEPT !["SA"] = "sa"]
      /\ UNCHANGED << AVar, BVar, BtoA, q >>

SA == sa

ra == /\ pc["RA"] = "ra"
      /\ BtoA # << >>
      /\ BtoA' = Tail(BtoA)
      /\ pc' = [pc EXCEPT !["RA"] = "ra"]
      /\ UNCHANGED << AVar, BVar, AtoB, q >>

RA == ra

sb == /\ pc["SB"] = "sb"
      /\ BtoA' = Append(BtoA, BVar[2])
      /\ pc' = [pc EXCEPT !["SB"] = "sb"]
      /\ UNCHANGED << AVar, BVar, AtoB, q >>

SB == sb

rb == /\ pc["RB"] = "rb"
      /\ AtoB # << >>
      /\ IF Head(AtoB)[2] # BVar[2]
            THEN BVar' = Head(AtoB)
            ELSE BVar' = BVar
      /\ AtoB' = Tail(AtoB)
      /\ pc' = [pc EXCEPT !["RB"] = "rb"]
      /\ UNCHANGED << AVar, BtoA, q >>

RB == rb

la == /\ pc["LA"] = "la"
      /\ AtoB # << >>
      /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
      /\ pc' = [pc EXCEPT !["LA"] = "la"]
      /\ UNCHANGED << AVar, BVar, BtoA, q >>

LA == la

lb == /\ pc["LB"] = "lb"
      /\ BtoA # << >>
      /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
      /\ pc' = [pc EXCEPT !["LB"] = "lb"]
      /\ UNCHANGED << AVar, BVar, AtoB, q >>

LB == lb

nd == /\ pc["ND"] = "nd"
      /\ AVar = BVar
      /\ q # << >>
      /\ AVar' = << Head(q), 1 - AVar[2] >>
      /\ q' = Tail(q)
      /\ pc' = [pc EXCEPT !["ND"] = "nd"]
      /\ UNCHANGED << BVar, AtoB, BtoA >>

ND == nd

pr == /\ pc["PR"] = "pr"
      /\ Len(q) < MaxQ
      /\ \E d \in Data : q' = Append(q, d)
      /\ pc' = [pc EXCEPT !["PR"] = "pr"]
      /\ UNCHANGED << AVar, BVar, AtoB, BtoA >>

PR == pr

Next == SA \/ RA \/ SB \/ RB \/ LA \/ LB \/ ND \/ PR

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(SA)
        /\ SF_vars(RA)
        /\ WF_vars(SB)
        /\ SF_vars(RB)
        /\ WF_vars(ND)
\* END TRANSLATION

-----------------------------------------------------------------------------
Msgs == Data \X {0, 1}

TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq({0, 1})
          /\ q \in Seq(Data)
          /\ Len(q) <= MaxQ
          /\ pc \in [ProcSet -> {"sa", "ra", "sb", "rb", "la", "lb", "nd", "pr"}]

\* Matching bits imply the receiver holds exactly the sender's value
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

\* Every value held by the sender is eventually delivered to the receiver
Delivery == \A v \in Msgs : (AVar = v) ~> (BVar = v)

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => Delivery
=============================================================================