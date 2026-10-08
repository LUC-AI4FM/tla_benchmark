------------------------------- MODULE DieHard -------------------------------

VARIABLES small, big

CONSTANTS smallCapacity, bigCapacity

smallCapacity == 3
bigCapacity   == 5

Init == /\ small = 0
        /\ big   = 0

FillSmall == /\ small < smallCapacity
             /\ small' = smallCapacity
             /\ big'   = big

FillBig == /\ big < bigCapacity
           /\ big'   = bigCapacity
           /\ small' = small

EmptySmall == /\ small > 0
              /\ small' = 0
              /\ big'   = big

EmptyBig == /\ big > 0
            /\ big'   = 0
            /\ small' = small

SmallToBig == /\ small > 0
               /\ big < bigCapacity
               /\ LET transferAmount == MIN(small, bigCapacity - big) IN
                  small' = small - transferAmount
                  /\ big'   = big + transferAmount

BigToSmall == /\ big > 0
               /\ small < smallCapacity
               /\ LET transferAmount == MIN(big, smallCapacity - small) IN
                  big'   = big - transferAmount
                  /\ small' = small + transferAmount

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

Spec == Init /\ [][Next]_<<small, big>>

TypeOK == /\ small \in 0..smallCapacity
          /\ big   \in 0..bigCapacity

HasFour == big = 4

PourAction == (small' # small) /\ (big' # big)

(*--algorithm DieHard
variables totalGallonsFilled = 0;

begin
    while TRUE do
        if \/ FillSmall
           \/ FillBig then
            totalGallonsFilled := totalGallonsFilled + 1;
        end if;
        await Next;
    end while;
end algorithm;*)

PostCondition ==
    /\ TLCGet("states") = 97
    /\ TLCGet("distinctStates") = 16
    /\ TLCGet("diameter") = 8
    /\ TLCGet("totalGallonsFilled") = 128

PossibleCounts ==
    /\ TLCGet("_POSSIBLE", HasFour) = 8
    /\ TLCGet("_POSSIBLE", PourAction) = 14

=============================================================================