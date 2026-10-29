---- MODULE ABPlusCal ----
EXTENDS Integers, Sequences

CONSTANT Data

ASSUME Data # {}

RemoveElement(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************
--algorithm ABPlusCal {
  variables AVar \in Data \X {1}, BVar = AVar,
            AtoB = << >>, BtoA = << >>, q = << >>;

  fair process (ASnd = "ASnd") {
    a: while (TRUE) { AtoB := Append(AtoB, AVar) }
  }

  fair+ process (ARcv = "ARcv") {
    b: while (TRUE) {
         await BtoA # << >>;
         if (Head(BtoA) = AVar[2] /\ q # << >>) {
           AVar := << Head(q), 1 - AVar[2] >>;
           q := Tail(q)
         };
         BtoA := Tail(BtoA)
       }
  }

  fair process (BSnd = "BSnd") {
    c: while (TRUE) { BtoA := Append(BtoA, BVar[2]) }
  }

  fair+ process (BRcv = "BRcv") {
    d: while (TRUE) {
         await AtoB # << >>;
         if (Head(AtoB)[2] # BVar[2]) { BVar := Head(AtoB) };
         AtoB := Tail(AtoB)
       }
  }

  process (LoseMsg = "LoseMsg") {
    e: while (TRUE) {
         either with (i \in 1..Len(AtoB)) { AtoB := RemoveElement(i, AtoB) }
         or     with (i \in 1..Len(BtoA)) { BtoA := RemoveElement(i, BtoA) }
       }
  }

  fair process (NewData = "NewData") {
    f: while (TRUE) {
         await AVar = BVar /\ q = << >>;
         with (v \in Data) { q := Append(q, v) }
       }
  }
}
***************************************************************************)

VARIABLES AVar, BVar, AtoB, BtoA, q

vars == << AVar, BVar, AtoB, BtoA, q >>

Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>
  /\ q = << >>

ASnd ==
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED << AVar, BVar, BtoA, q >>

ARcv ==
  /\ BtoA # << >>
  /\ IF Head(BtoA) = AVar[2] /\ q # << >>
       THEN /\ AVar' = << Head(q), 1 - AVar[2] >>
            /\ q' = Tail(q)
       ELSE /\ UNCHANGED << AVar, q >>
  /\ BtoA' = Tail(BtoA)
  /\ UNCHANGED << BVar, AtoB >>

BSnd ==
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED << AVar, BVar, AtoB, q >>

BRcv ==
  /\ AtoB # << >>
  /\ IF Head(AtoB)[2] # BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE UNCHANGED BVar
  /\ AtoB' = Tail(AtoB)
  /\ UNCHANGED << AVar, BtoA, q >>

LoseMsg ==
  /\ \/ \E i \in 1..Len(AtoB) :
          /\ AtoB' = RemoveElement(i, AtoB)
          /\ UNCHANGED BtoA
     \/ \E i \in 1..Len(BtoA) :
          /\ BtoA' = RemoveElement(i, BtoA)
          /\ UNCHANGED AtoB
  /\ UNCHANGED << AVar, BVar, q >>

NewData ==
  /\ AVar = BVar
  /\ q = << >>
  /\ \E v \in Data : q' = Append(q, v)
  /\ UNCHANGED << AVar, BVar, AtoB, BtoA >>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg \/ NewData

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ASnd)
  /\ SF_vars(ARcv)
  /\ WF_vars(BSnd)
  /\ SF_vars(BRcv)
  /\ WF_vars(NewData)

-----------------------------------------------------------------------------

Messages == (Data \X {0, 1}) \cup {0, 1}

TypeOK ==
  /\ AVar \in Data \X {0, 1}
  /\ BVar \in Data \X {0, 1}
  /\ AtoB \in Seq(Data \X {0, 1})
  /\ BtoA \in Seq({0, 1})
  /\ q \in Seq(Data)
  /\ Len(q) <= 1

Inv ==
  /\ TypeOK
  /\ (AVar[2] = BVar[2]) => (AVar = BVar)
  /\ \A i \in 1..Len(AtoB) :
       (AtoB[i][2] = AVar[2]) => (AtoB[i] = AVar)

Liveness ==
  \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

=============================================================================