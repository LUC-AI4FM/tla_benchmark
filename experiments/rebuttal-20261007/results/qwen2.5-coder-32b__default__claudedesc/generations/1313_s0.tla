------------------------------- MODULE DieHard -------------------------------
EXTENDS Naturals, TLC

CONSTANTS smallCapacity, bigCapacity
VARIABLES small, big, totalGallonsFilled

Init == /\ small = 0 
        /\ big = 0 
        /\ totalGallonsFilled = 0

FillSmall == /\ small' < smallCapacity 
             /\ small' = smallCapacity 
             /\ big' = big 
             /\ totalGallonsFilled' = totalGallonsFilled + smallCapacity - small

FillBig == /\ big' < bigCapacity 
           /\ big' = bigCapacity 
           /\ small' = small 
           /\ totalGallonsFilled' = totalGallonsFilled + bigCapacity - big

EmptySmall == /\ small' = 0 
              /\ big' = big 
              /\ totalGallonsFilled' = totalGallonsFilled

EmptyBig == /\ big' = 0 
            /\ small' = small 
            /\ totalGallonsFilled' = totalGallonsFilled

SmallToBig == /\ big + (smallCapacity - small) >= bigCapacity
              /\ small' = small - (bigCapacity - big)
              /\ big' = bigCapacity
              /\ totalGallonsFilled' = totalGallonsFilled

\* SmallToBig alternative when destination is not full
SmallToBig2 == /\ big + (smallCapacity - small) < bigCapacity
               /\ small' = 0
               /\ big' = big + (smallCapacity - small)
               /\ totalGallonsFilled' = totalGallonsFilled

BigToSmall == /\ small + (bigCapacity - big) >= smallCapacity
              /\ big' = big - (smallCapacity - small)
              /\ small' = smallCapacity
              /\ totalGallonsFilled' = totalGallonsFilled

\* BigToSmall alternative when destination is not full
BigToSmall2 == /\ small + (bigCapacity - big) < smallCapacity
               /\ big' = 0
               /\ small' = small + (bigCapacity - big)
               /\ totalGallonsFilled' = totalGallonsFilled

Next == \/ FillSmall 
        \/ FillBig 
        \/ EmptySmall 
        \/ EmptyBig 
        \/ SmallToBig \/ SmallToBig2 
        \/ BigToSmall \/ BigToSmall2

Spec == Init /\ [][Next]_<<small, big, totalGallonsFilled>>

TypeOK == /\ small \in 0..smallCapacity
          /\ big \in 0..bigCapacity

HasFour == big = 4

PourAction == (small' # small) /\ (big' # big)

THEOREM Spec => []TypeOK

THEOREM Spec => <>HasFour

THEOREM Spec => <>(PourAction)

TLC_POSTCONDITIONS ==
    /\ TLCGet("states") = 97
    /\ TLCGet("distinct-states") = 16
    /\ TLCGet("diameter") = 8
    /\ TLCGet("totalGallonsFilled") = 128

POSSIBLE HasFour, PourAction

THEOREM Spec => _<<HasFour>>_ = 8

THEOREM Spec => _<<PourAction>>_ = 14

=============================================================================