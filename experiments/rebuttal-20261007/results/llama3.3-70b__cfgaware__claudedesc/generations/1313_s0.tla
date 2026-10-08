---------------------------- MODULE DieHard --------------------------------
EXTENDS Integers

CONSTANT SmallCapacity, BigCapacity
VARIABLE small, big, filledGallons

TypeOK == (small >= 0 /\ small <= SmallCapacity) /\ (big >= 0 /\ big <= BigCapacity)

HasFour == big = 4

PourAction == (small' < small /\ big' > big) \/ (small' > small /\ big' < big)

FillSmall == small' = SmallCapacity /\ big' = big
FillBig == small' = small /\ big' = BigCapacity

EmptySmall == small' = 0 /\ big' = big
EmptyBig == small' = small /\ big' = 0

SmallToBig == 
  IF small + big <= BigCapacity 
  THEN small' = 0 /\ big' = small + big 
  ELSE small' = small - (BigCapacity - big) /\ big' = BigCapacity

BigToSmall == 
  IF big + small <= SmallCapacity 
  THEN big' = 0 /\ small' = big + small 
  ELSE big' = big - (SmallCapacity - small) /\ small' = SmallCapacity

Next == FillSmall \/ FillBig \/ EmptySmall \/ EmptyBig \/ SmallToBig \/ BigToSmall
Spec == Init /\ [][Next]_<<small, big>>
Init == (small = 0 /\ big = 0)

FilledGallonsUpdate == 
  IF FillSmall THEN filledGallons' = filledGallons + SmallCapacity - small
  ELSE IF FillBig THEN filledGallons' = filledGallons + BigCapacity - big
  ELSE filledGallons' = filledGallons

NextWithFilledGallons == (FillSmall /\ FilledGallonsUpdate) \/ 
                         (FillBig /\ FilledGallonsUpdate) \/ 
                         (EmptySmall /\ filledGallons' = filledGallons) \/ 
                         (EmptyBig /\ filledGallons' = filledGallons) \/ 
                         (SmallToBig /\ filledGallons' = filledGallons) \/ 
                         (BigToSmall /\ filledGallons' = filledGallons)

SpecWithFilledGallons == Init /\ [][NextWithFilledGallons]_<<small, big, filledGallons>>

PostCondition == <<97, 16, 8, 128>> = <<NumStates, NumDistinctStates, Diameter, TotalGallonsUsed>>
PossibleCounts == <<8, 14>> = <<HasFourCount, PourActionCount>>

THEOREM Spec => []TypeOK
THEOREM Spec => PostCondition

=============================================================================