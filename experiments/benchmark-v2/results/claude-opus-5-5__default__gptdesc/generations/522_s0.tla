--------------------------- MODULE ABProtocol ---------------------------
EXTENDS Integers, Sequences

CONSTANT Data

ASSUME Data # {}

Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************
--algorithm ABProtocol
    variables AVar \in [data : Data, bit : {0}],
              BVar = AVar,
              AtoB = << >>,
              BtoA = << >>;

    fair process (A = "A")
    begin
    a:  while TRUE do
          either AtoB := Append(AtoB, AVar)
          or     await BtoA # << >>;
                 if Head(BtoA) = AVar.bit then
                   with d \in Data do
                     AVar := [data |-> d, bit |-> 1 - AVar.bit]
                   end with
                 end if;
                 BtoA := Tail(BtoA)
          end either
        end while
    end process

    fair process (B = "B")
    begin
    b:  while TRUE do
          either BtoA := Append(BtoA, BVar.bit)
          or     await AtoB # << >>;
                 if Head(AtoB).bit # BVar.bit then
                   BVar := Head(AtoB)
                 end if;
                 AtoB := Tail(AtoB)
          end either
        end while
    end process

    process (LoseMsg = "L")
    begin
    c:  while TRUE do
          either with i \in 1..Len(AtoB) do
                   AtoB := Remove(i, AtoB)
                 end with
          or     with i \in 1..Len(BtoA) do
                   BtoA := Remove(i, BtoA)
                 end with
          end either
        end while
    end process
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES AVar, BVar, AtoB, BtoA

vars == << AVar, BVar, AtoB, BtoA >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == /\ AVar \in [data : Data, bit : {0}]
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

A == \/ /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED << AVar, BVar, BtoA >>
     \/ /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar.bit
              THEN \E d \in Data : AVar' = [data |-> d, bit |-> 1 - AVar.bit]
              ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar, AtoB >>

B == \/ /\ BtoA' = Append(BtoA, BVar.bit)
        /\ UNCHANGED << AVar, BVar, AtoB >>
     \/ /\ AtoB # << >>
        /\ IF Head(AtoB).bit # BVar.bit
              THEN BVar' = Head(AtoB)
              ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED << AVar, BtoA >>

LoseMsg == \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
              /\ UNCHANGED << AVar, BVar, BtoA >>
           \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
              /\ UNCHANGED << AVar, BVar, AtoB >>

Next == A \/ B \/ LoseMsg

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)
\* END TRANSLATION

-----------------------------------------------------------------------------
Messages == [data : Data, bit : {0, 1}]

TypeOK == /\ AVar \in Messages
          /\ BVar \in Messages
          /\ AtoB \in Seq(Messages)
          /\ BtoA \in Seq({0, 1})

\* When B holds the same bit as A, B holds exactly A's current message.
Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

\* Any message in transit carrying A's current bit carries A's current data.
ChannelInv == \A i \in 1..Len(AtoB) :
                 (AtoB[i].bit = AVar.bit) => (AtoB[i] = AVar)

THEOREM Spec => [](TypeOK /\ Inv /\ ChannelInv)
=============================================================================