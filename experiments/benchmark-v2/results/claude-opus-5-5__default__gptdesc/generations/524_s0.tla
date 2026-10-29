---------------------------- MODULE ABPCal ----------------------------
EXTENDS Integers, Sequences

CONSTANTS Data

ASSUME Data # {}

Remove(i, seq) == [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

(***************************************************************************
--algorithm ABPCal {
  variables AVar \in Data \X {1},
            BVar = AVar,
            AtoB = << >>,
            BtoA = << >>,
            queue = << >> ;

  fair process (ASnd = "ASnd") {
    a: while (TRUE) { AtoB := Append(AtoB, AVar) }
  }

  fair+ process (ARcv = "ARcv") {
    b: while (TRUE) {
         await BtoA # << >> /\ (Head(BtoA) = AVar[2] => queue # << >>) ;
         if (Head(BtoA) = AVar[2]) {
           AVar := << Head(queue), 1 - AVar[2] >> ;
           queue := Tail(queue)
         } ;
         BtoA := Tail(BtoA)
       }
  }

  fair process (BSnd = "BSnd") {
    c: while (TRUE) { BtoA := Append(BtoA, BVar[2]) }
  }

  fair+ process (BRcv = "BRcv") {
    d: while (TRUE) {
         await AtoB # << >> ;
         if (Head(AtoB)[2] # BVar[2]) { BVar := Head(AtoB) } ;
         AtoB := Tail(AtoB)
       }
  }

  process (LoseMsg = "LoseMsg") {
    e: while (TRUE) {
         either with (i \in 1..Len(AtoB)) { AtoB := Remove(i, AtoB) }
         or     with (i \in 1..Len(BtoA)) { BtoA := Remove(i, BtoA) }
       }
  }

  fair process (NewData = "NewData") {
    f: while (TRUE) {
         await AVar = BVar /\ queue = << >> ;
         with (v \in Data) { queue := Append(queue, v) }
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES AVar, BVar, AtoB, BtoA, queue

vars == << AVar, BVar, AtoB, BtoA, queue >>

ProcSet == {"ASnd"} \cup {"ARcv"} \cup {"BSnd"} \cup {"BRcv"} \cup {"LoseMsg"} \cup {"NewData"}

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>
        /\ queue = << >>

ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED << AVar, BVar, BtoA, queue >>

ARcv == /\ BtoA # << >>
        /\ Head(BtoA) = AVar[2] => queue # << >>
        /\ IF Head(BtoA) = AVar[2]
              THEN /\ AVar' = << Head(queue), 1 - AVar[2] >>
                   /\ queue' = Tail(queue)
              ELSE /\ UNCHANGED << AVar, queue >>
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar, AtoB >>

BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED << AVar, BVar, AtoB, queue >>

BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
              THEN BVar' = Head(AtoB)
              ELSE UNCHANGED BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED << AVar, BtoA, queue >>

LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
                 /\ UNCHANGED BtoA
              \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
                 /\ UNCHANGED AtoB
           /\ UNCHANGED << AVar, BVar, queue >>

NewData == /\ AVar = BVar
           /\ queue = << >>
           /\ \E v \in Data : queue' = Append(queue, v)
           /\ UNCHANGED << AVar, BVar, AtoB, BtoA >>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg \/ NewData

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ASnd)
        /\ SF_vars(ARcv)
        /\ WF_vars(BSnd)
        /\ SF_vars(BRcv)
        /\ WF_vars(NewData)
\* END TRANSLATION

-----------------------------------------------------------------------------
Messages == Data \X {0, 1}

TypeOK == /\ AVar \in Messages
          /\ BVar \in Messages
          /\ AtoB \in Seq(Messages)
          /\ BtoA \in Seq({0, 1})
          /\ queue \in Seq(Data)

Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

Liveness == \A v \in Messages : (AVar = v) ~> (BVar = v)

THEOREM Spec => [](TypeOK /\ Inv)
=============================================================================