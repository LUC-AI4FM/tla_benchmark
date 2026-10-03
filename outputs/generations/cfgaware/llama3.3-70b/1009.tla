--------------------------- MODULE BufferedFile ---------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Symbols, ArbitrarySymbol, MaxOffset, BuffSz

VARIABLES fileOnDisk, buffer, offset, length

TypeOK == (fileOnDisk \in [1..MaxOffset -> Symbols]) /\ 
          (buffer \in [1..BuffSz -> Symbols]) /\ 
          (offset \in 0..MaxOffset) /\ 
          (length \in 0..MaxOffset)

Inv1 == offset <= length

Inv2CanAlwaysBeRestored == 
  <<fileOnDisk, buffer, offset, length>> =<<
    [fileOnDisk |-> fileOnDisk,
     buffer |-> buffer,
     offset |-> 0,
     length |-> length]>> => 
  (buffer = <<>>) /\ (offset = 0)

Inv3 == 
  (offset + BuffSz > length) => 
  (buffer = Take(BuffSz, Drop(offset, fileOnDisk)))

Inv4 == 
  (offset + BuffSz <= length) => 
  (Take(BuffSz, Drop(offset, buffer)) = Take(BuffSz, Drop(offset, fileOnDisk)))

Inv5 == offset >= 0

Seek(op) == 
  /\ op \in 0..MaxOffset
  /\ offset' = op
  /\ buffer' = IF op + BuffSz > length THEN Take(BuffSz, Drop(op, fileOnDisk)) ELSE <<>>
  /\ fileOnDisk' = fileOnDisk
  /\ length' = length

Write1(symbol) == 
  /\ symbol \in Symbols
  /\ offset < MaxOffset
  /\ buffer' = Append(buffer, symbol)
  /\ IF offset + Len(buffer') > length THEN fileOnDisk' = Append(fileOnDisk, symbol) ELSE fileOnDisk' = fileOnDisk
  /\ offset' = offset + 1
  /\ length' = IF offset + 1 > length THEN offset + 1 ELSE length

Read1 == 
  /\ offset < length
  /\ buffer' = Tail(buffer)
  /\ fileOnDisk' = fileOnDisk
  /\ offset' = offset + 1
  /\ length' = length

WriteAtMost(symbols) == 
  /\ symbols \in Seq(Symbols)
  /\ Len(symbols) <= MaxOffset - offset
  /\ buffer' = Append(buffer, symbols)
  /\ IF offset + Len(buffer') > length THEN fileOnDisk' = Append(fileOnDisk, symbols) ELSE fileOnDisk' = fileOnDisk
  /\ offset' = offset + Len(symbols)
  /\ length' = IF offset + Len(symbols) > length THEN offset + Len(symbols) ELSE length

ReadCorrect == 
  /\ offset < length
  /\ buffer' = Tail(buffer)
  /\ fileOnDisk' = fileOnDisk
  /\ offset' = offset + 1
  /\ length' = length

FlushBuffer == 
  /\ fileOnDisk' = Append(fileOnDisk, buffer)
  /\ buffer' = <<>>
  /\ offset' = 0
  /\ length' = IF length > Len(fileOnDisk) THEN length ELSE Len(fileOnDisk)

SetLength(newLength) == 
  /\ newLength \in 0..MaxOffset
  /\ fileOnDisk' = Take(newLength, fileOnDisk)
  /\ buffer' = <<>>
  /\ offset' = 0
  /\ length' = newLength

Next == 
  \/ \E op \in 0..MaxOffset : Seek(op)
  \/ \E symbol \in Symbols : Write1(symbol)
  \/ Read1
  \/ \E symbols \in Seq(Symbols) : WriteAtMost(symbols)
  \/ FlushBuffer
  \/ \E newLength \in 0..MaxOffset : SetLength(newLength)

Spec == 
  /\ TypeOK
  /\ [][Next]_<<fileOnDisk, buffer, offset, length>>

Safety == Spec

FlushBufferCorrect == 
  Spec => []Inv1

SeekCorrect == 
  Spec => []Inv2CanAlwaysBeRestored

SeekEstablishesInv2 == 
  Spec => [](SeekCorrect => Inv2CanAlwaysBeRestored)

Write1Correct == 
  Spec => []Inv3

Read1Correct == 
  Spec => []Inv4

WriteAtMostCorrect == 
  Spec => []Inv5

THEOREM Spec => Safety
THEOREM Spec => FlushBufferCorrect
THEOREM Spec => SeekCorrect
THEOREM Spec => SeekEstablishesInv2
THEOREM Spec => Write1Correct
THEOREM Spec => Read1Correct
THEOREM Spec => WriteAtMostCorrect

=============================================================================