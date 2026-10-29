--------------------------- MODULE AlternatingBit ---------------------------
(***************************************************************************)
(* The Alternating Bit protocol, without liveness requirements.            *)
(* Sender A sends data messages over channel AtoB.                         *)
(* Receiver B sends acknowledgements over channel BtoA.                    *)
(* Process LoseMsgs can drop any message from either channel.              *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data

(***************************************************************************
--algorithm ABProtocol
    variables AVar \in Data \X {1}, BVar = AVar,
              AtoB = << >>, BtoA = << >> ;
    define
      Remove(i, seq) ==
        [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]
    end define ;

    process A = "A"
    begin a: while TRUE do
               either AtoB := Append(AtoB, AVar) ;
               or     await BtoA # << >> ;
                      if Head(BtoA) = AVar[2]
                        then with d \in Data do
                               AVar := <<d, 1 - AVar[2]>>
                             end with ;
                      end if ;
                      BtoA := Tail(BtoA) ;
               end either ;
             end while ;
    end process

    process B = "B"
    begin b: while TRUE do
               either BtoA := Append(BtoA, BVar[2]) ;
               or     await AtoB # << >> ;
                      if Head(AtoB)[2] # BVar[2]
                        then BVar := Head(AtoB) ;
                      end if ;
                      AtoB := Tail(AtoB) ;
               end either ;
             end while ;
    end process

    process LoseMsgs = "L"
    begin c: while TRUE do
               either with i \in 1..Len(AtoB) do
                        AtoB := Remove(i, AtoB)
                      end with ;
               or     with i \in 1..Len(BtoA) do
                        BtoA := Remove(i, BtoA)
                      end with ;
               end either ;
             end while ;
    end process
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES AVar, BVar, AtoB, BtoA

Remove(i, seq) ==
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

vars == << AVar, BVar, AtoB, BtoA >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

A == \/ /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED << AVar, BVar, BtoA >>
     \/ /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar, AtoB >>

B == \/ /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED << AVar, BVar, AtoB >>
     \/ /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED << AVar, BtoA >>

LoseMsgs == \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
               /\ UNCHANGED << AVar, BVar, BtoA >>
            \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
               /\ UNCHANGED << AVar, BVar, AtoB >>

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
Messages == Data \X {0, 1}

TypeOK == /\ AVar \in Messages
          /\ BVar \in Messages
          /\ AtoB \in Seq(Messages)
          /\ BtoA \in Seq({0, 1})

\* When B holds the same bit as A, B has received A's current data.
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

THEOREM Spec => [](TypeOK /\ Inv)
=============================================================================