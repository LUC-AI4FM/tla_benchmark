---------------------------- MODULE ABSpec ----------------------------
EXTENDS Integers

CONSTANT Data

(***************************************************************************
--algorithm ABSpec {
  variables AVar \in Data \X {1}, BVar = AVar ;

  fair process (A = "A") {
    a: while (TRUE) {
         await AVar[2] = BVar[2] ;
         with (d \in Data) { AVar := <<d, 1 - AVar[2]>> }
       }
  }

  fair process (B = "B") {
    b: while (TRUE) {
         await AVar[2] # BVar[2] ;
         BVar := AVar
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES AVar, BVar

vars == << AVar, BVar >>

ProcSet == {"A"} \cup {"B"}

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar

A == /\ AVar[2] = BVar[2]
     /\ \E d \in Data :
          AVar' = <<d, 1 - AVar[2]>>
     /\ BVar' = BVar

B == /\ AVar[2] # BVar[2]
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)
\* END TRANSLATION

-----------------------------------------------------------------------------
TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}

\* When the bits agree, B has received A's current value.
Consistent == (AVar[2] = BVar[2]) => (AVar = BVar)

Inv == TypeOK /\ Consistent

\* Liveness: every value sent by A is eventually received by B.
Delivery == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

\* Both processes keep making progress forever.
Progress == /\ []<>(AVar[2] = BVar[2])
            /\ []<>(AVar[2] # BVar[2])
=============================================================================