--------------------------- MODULE BufferedRandomAccessFile ---------------------------
EXTENDS Integers, Sequences

CONSTANTS MaxOffset, BuffSz
VARIABLES dirty, length, curr, lo, buff, diskPos, file_content, file_pointer

TypeOK == /\ dirty \in {TRUE, FALSE}
           /\ length \in 0..MaxOffset + BuffSz
           /\ curr \in 0..length
           /\ lo \in 0..MaxOffset
           /\ buff \in [1..BuffSz -> 0..255]
           /\ diskPos \in 0..MaxOffset

Inv1 == dirty = (buff /= <<>>)
Inv2 == lo <= curr /\ curr < lo + BuffSz
Inv3 == file_content = [i \in 0..length |-> IF i < lo OR i >= lo + BuffSz THEN file_content[i] ELSE buff[i - lo]]
Inv4 == length = IF dirty THEN (lo + BuffSz) ELSE length
Inv5 == diskPos = lo

LogicalFileContent == [i \in 0..length |-> IF i < lo OR i >= lo + BuffSz THEN file_content[i] ELSE buff[i - lo]]

Init == /\ dirty = FALSE
          /\ length = 0
          /\ curr = 0
          /\ lo = 0
          /\ buff = <<>>
          /\ diskPos = 0
          /\ file_content = [i \in 0..MaxOffset + BuffSz |-> 0]
          /\ file_pointer = 0

FlushBuffer == IF dirty THEN
                 /\ dirty' = FALSE
                 /\ length' = length
                 /\ curr' = curr
                 /\ lo' = lo
                 /\ buff' = buff
                 /\ diskPos' = lo
                 /\ file_content' = [file_content EXCEPT ![i \in lo..lo + BuffSz - 1] = buff[i - lo]]
                 /\ file_pointer' = file_pointer
              ELSE
                 /\ dirty' = dirty
                 /\ length' = length
                 /\ curr' = curr
                 /\ lo' = lo
                 /\ buff' = buff
                 /\ diskPos' = diskPos
                 /\ file_content' = file_content
                 /\ file_pointer' = file_pointer

Seek == IF curr < lo OR curr >= lo + BuffSz THEN
          /\ dirty' = FALSE
          /\ length' = length
          /\ curr' = curr
          /\ lo' = IF curr < lo THEN curr - (BuffSz \div 2) ELSE curr - BuffSz + 1
          /\ buff' = [i \in 1..BuffSz |-> file_content[lo' + i - 1]]
          /\ diskPos' = lo'
          /\ file_content' = file_content
          /\ file_pointer' = file_pointer
       ELSE
          /\ dirty' = dirty
          /\ length' = length
          /\ curr' = curr
          /\ lo' = lo
          /\ buff' = buff
          /\ diskPos' = diskPos
          /\ file_content' = file_content
          /\ file_pointer' = file_pointer

SetLength == /\ dirty' = FALSE
               /\ length' \in 0..MaxOffset + BuffSz
               /\ curr' = IF length' < curr THEN length' ELSE curr
               /\ lo' = lo
               /\ buff' = [i \in 1..BuffSz |-> IF i - 1 < length' - lo THEN file_content[lo + i - 1] ELSE 0]
               /\ diskPos' = diskPos
               /\ file_content' = [file_content EXCEPT ![i \in length'..MaxOffset + BuffSz - 1] = 0]
               /\ file_pointer' = file_pointer

Read1 == /\ dirty' = dirty
           /\ length' = length
           /\ curr' = curr + 1
           /\ lo' = lo
           /\ buff' = buff
           /\ diskPos' = diskPos
           /\ file_content' = file_content
           /\ file_pointer' = file_pointer

Write1 == /\ dirty' = TRUE
            /\ length' = IF curr >= length THEN curr + 1 ELSE length
            /\ curr' = curr + 1
            /\ lo' = lo
            /\ buff' = [buff EXCEPT ![curr - lo] = SOME 0..255]
            /\ diskPos' = diskPos
            /\ file_content' = file_content
            /\ file_pointer' = file_pointer

Read == /\ dirty' = dirty
          /\ length' = length
          /\ curr' = curr + 1
          /\ lo' = lo
          /\ buff' = buff
          /\ diskPos' = diskPos
          /\ file_content' = file_content
          /\ file_pointer' = file_pointer

WriteAtMost == /\ dirty' = TRUE
                 /\ length' = IF curr >= length THEN curr + 1 ELSE length
                 /\ curr' = curr + 1
                 /\ lo' = lo
                 /\ buff' = [buff EXCEPT ![curr - lo] = SOME 0..255]
                 /\ diskPos' = diskPos
                 /\ file_content' = file_content
                 /\ file_pointer' = file_pointer

Symbols == {ArbitrarySymbol}

Spec == Init /\ [][Next]_<<dirty, length, curr, lo, buff, diskPos, file_content, file_pointer>>
Next == \/ FlushBuffer
         \/ Seek
         \/ SetLength
         \/ Read1
         \/ Write1
         \/ Read
         \/ WriteAtMost

FlushBufferCorrect == \A curr, lo, buff, dirty, length, file_content :
                       /\ Inv2
                       /\ dirty
                       /\ FlushBuffer
                       ==> \E file_content' :
                              /\ file_content' = [file_content EXCEPT ![i \in lo..lo + BuffSz - 1] = buff[i - lo]]
                              /\ Inv3

SeekCorrect == \A curr, lo, buff, dirty, length, file_content :
                 /\ Seek
                 ==> \E lo', buff' :
                        /\ lo' = IF curr < lo THEN curr - (BuffSz \div 2) ELSE curr - BuffSz + 1
                        /\ buff' = [i \in 1..BuffSz |-> file_content[lo' + i - 1]]
                        /\ Inv2

SeekEstablishesInv2 == \A curr, lo, buff, dirty, length, file_content :
                         /\ Seek
                         ==> Inv2'

Write1Correct == \A curr, lo, buff, dirty, length, file_content :
                   /\ Write1
                   ==> \E buff' :
                          /\ buff' = [buff EXCEPT ![curr - lo] = SOME 0..255]
                          /\ Inv4

Read1Correct == \A curr, lo, buff, dirty, length, file_content :
                  /\ Read1
                  ==> \E curr' :
                         /\ curr' = curr + 1
                         /\ Inv5

WriteAtMostCorrect == \A curr, lo, buff, dirty, length, file_content :
                        /\ WriteAtMost
                        ==> \E buff' :
                               /\ buff' = [buff EXCEPT ![curr - lo] = SOME 0..255]
                               /\ Inv4

ReadCorrect == \A curr, lo, buff, dirty, length, file_content :
                 /\ Read
                 ==> \E curr' :
                        /\ curr' = curr + 1
                        /\ Inv5

Inv2CanAlwaysBeRestored == \A lo, buff, dirty, length, file_content :
                             /\ Inv2
                             ==> \E lo', buff' :
                                    /\ lo' = IF curr < lo THEN curr - (BuffSz \div 2) ELSE curr - BuffSz + 1
                                    /\ buff' = [i \in 1..BuffSz |-> file_content[lo' + i - 1]]
                                    /\ Inv2

Safety == []Inv1 /\ []Inv2 /\ []Inv3 /\ []Inv4 /\ []Inv5
=============================================================================