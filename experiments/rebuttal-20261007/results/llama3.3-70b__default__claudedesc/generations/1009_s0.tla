```tla
MODULE BufferedRandomAccessFile
EXTENDS Integers, Sequences, TLC

CONSTANTS MaxOffset, BuffSz

VARIABLES dirty, length, curr, lo, buff, diskPos, file_content, file_pointer

Inv1 == dirty = (buff /= <<>>)
Inv2 == lo <= curr /\ curr < lo + BuffSz
Inv3 == buff = Take(BuffSz, Drop(lo, file_content)) \/ <<>>
Inv4 == length >= 0
Inv5 == file_pointer = IF dirty THEN lo ELSE diskPos

LogicalFileContent ==
  LET bufferOverlay == Take(length, Append(buff, Replicate(MaxOffset - (lo + BuffSz), 0)))
  IN Append(Take(lo, file_content), bufferOverlay)

Init ==
  /\ dirty = FALSE
  /\ length = 0
  /\ curr = 0
  /\ lo = 0
  /\ buff = <<>>
  /\ diskPos = 0
  /\ file_content = <<>>
  /\ file_pointer = 0

FlushBuffer ==
  /\ dirty
  /\ file_content' = Append(Take(lo, file_content), Append(buff, Drop(lo + BuffSz, file_content)))
  /\ buff' = <<>>
  /\ dirty' = FALSE
  /\ lo' = lo
  /\ curr' = curr
  /\ length' = length
  /\ diskPos' = lo
  /\ file_pointer' = lo

Seek ==
  \/ \* flush and refill buffer if seek position is outside the buffered window
    (curr' \in lo .. lo + BuffSz - 1)
    /\ dirty'
    /\ buff' = Take(BuffSz, Drop(lo, file_content))
    /\ lo' = lo
    /\ length' = length
    /\ diskPos' = diskPos
    /\ file_pointer' = curr'
  \/ \* refill buffer if seek position is outside the buffered window
    (curr' < lo)
    /\ dirty' = FALSE
    /\ buff' = Take(BuffSz, Drop(curr', file_content))
    /\ lo' = curr'
    /\ length' = length
    /\ diskPos' = curr'
    /\ file_pointer' = curr'
  \/ \* refill buffer if seek position is outside the buffered window
    (curr' >= lo + BuffSz)
    /\ dirty' = FALSE
    /\ buff' = Take(BuffSz, Drop(curr' - BuffSz + 1, file_content))
    /\ lo' = curr' - BuffSz + 1
    /\ length' = length
    /\ diskPos' = curr'
    /\ file_pointer' = curr'

SetLength ==
  /\ length' \in 0 .. MaxOffset
  /\ IF length' < length THEN
      buff' = Take(length', buff)
    ELSE
      buff' = Append(buff, Replicate(length' - length, 0))
  /\ dirty' = (length' > length) OR dirty
  /\ lo' = lo
  /\ curr' = Min(curr, length')
  /\ diskPos' = diskPos
  /\ file_pointer' = IF length' < length THEN Min(file_pointer, length') ELSE file_pointer

Read1 ==
  /\ curr' = curr + 1
  /\ buff' = buff
  /\ dirty' = dirty
  /\ lo' = lo
  /\ length' = length
  /\ diskPos' = diskPos
  /\ file_pointer' = file_pointer

Write1 ==
  /\ buff' = Append(Take(BuffSz - 1, buff), 0)
  /\ dirty' = TRUE
  /\ lo' = lo
  /\ curr' = curr + 1
  /\ length' = IF curr + 1 > length THEN curr + 1 ELSE length
  /\ diskPos' = diskPos
  /\ file_pointer' = file_pointer

Read ==
  /\ buff' = buff
  /\ dirty' = dirty
  /\ lo' = lo
  /\ curr' = curr + 1
  /\ length' = length
  /\ diskPos' = diskPos
  /\ file_pointer' = file_pointer

WriteAtMost ==
  /\ buff' = Append(Take(BuffSz - 1, buff), 0)
  /\ dirty' = TRUE
  /\ lo' = lo
  /\ curr' = curr + 1
  /\ length' = IF curr + 1 > length THEN curr + 1 ELSE length
  /\ diskPos' = diskPos
  /\ file_pointer' = file_pointer

Next ==
  \/ FlushBuffer
  \/ Seek
  \/ SetLength
  \/ Read1
  \/ Write1
  \/ Read
  \/ WriteAtMost
  \/ \* stuttering
    (dirty' = dirty)
    /\ (length' = length)
    /\ (curr' = curr)
    /\ (lo' = lo)
    /\ (buff' = buff)
    /\ (diskPos' = diskPos)
    /\ (file_pointer' = file_pointer)

Spec == Init /\ [][Next]_<<dirty, length, curr, lo, buff, diskPos, file_content, file_pointer>>
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []Inv4
THEOREM Spec => []Inv5

TemporalProperties ==
  /\ [][Next -> (Spec' => Inv2)]
  /\ WF_Vars(FlushBuffer)
  /\ WF_Vars(Seek)

ModelCheck ==
  /\ MaxOffset = 3
  /\ BuffSz = 2
```