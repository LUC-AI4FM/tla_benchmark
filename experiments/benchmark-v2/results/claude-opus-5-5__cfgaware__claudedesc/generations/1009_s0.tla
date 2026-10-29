```tla
os

FillBuff(content, pos) ==
    [i \in 0..(BuffSz-1) |->
        IF pos + i < Len(content) THEN content[pos + i] ELSE ArbitrarySymbol]
FillPos(content, pos) ==
    IF pos < Len(content) THEN Min(pos + BuffSz, Len(content)) ELSE pos

\* State after (possibly) flushing and refilling so that curr lies in the window
NeedFill == curr < lo \/ curr >= lo + BuffSz
C1 == IF NeedFill THEN FlushedContent ELSE file_content
B1 == IF NeedFill THEN FillBuff(FlushedContent, curr) ELSE buff
Lo1 == IF NeedFill THEN curr ELSE lo
D1 == IF NeedFill THEN FillPos(FlushedContent, curr) ELSE diskPos
Dirty1 == IF NeedFill THEN FALSE ELSE dirty
Hi1 == Min(Lo1 + BuffSz, length)

-----------------------------------------------------------------------------
(* Actions *)

FlushBuffer ==
    /\ dirty
    /\ file_content' = WriteToFile(file_content, lo, FlushedData)
    /\ file_pointer' = lo + FlushLen
    /\ diskPos' = lo + FlushLen
    /\ dirty' = FALSE
    /\ UNCHANGED <<length, curr, lo, buff>>

Seek(pos) ==
    /\ curr' = pos
    /\ IF lo <= pos /\ pos < lo + BuffSz
          THEN UNCHANGED <<dirty, length, lo, buff, diskPos, file_content, file_pointer>>
          ELSE /\ file_content' = FlushedContent
               /\ buff' = FillBuff(FlushedContent, pos)
               /\ lo' = pos
               /\ diskPos' = FillPos(FlushedContent, pos)
               /\ file_pointer' = FillPos(FlushedContent, pos)
               /\ dirty' = FALSE
               /\ UNCHANGED length

SetLength(n) ==
    /\ file_content' = SetFileLength(FlushedContent, n)
    /\ diskPos' = Min(FlushedPos, n)
    /\ file_pointer' = Min(FlushedPos, n)
    /\ length' = n
    /\ curr' = Min(curr, n)
    /\ dirty' = FALSE
    /\ buff' = [i \in 0..(BuffSz-1) |-> IF lo + i < n THEN buff[i] ELSE ArbitrarySymbol]
    /\ UNCHANGED lo

ReadData(n) ==
    LET k == Min(n, Hi1 - curr)
    IN [i \in 0..(k-1) |-> B1[curr - Lo1 + i]]

Read(n) ==
    /\ curr < length
    /\ buff' = B1
    /\ lo' = Lo1
    /\ file_content' = C1
    /\ diskPos' = D1
    /\ file_pointer' = D1
    /\ dirty' = Dirty1
    /\ curr' = curr + Len(ReadData(n))
    /\ UNCHANGED length

Read1 == Read(1)

Write1(s) ==
    /\ curr < MaxOffset
    /\ buff' = [B1 EXCEPT ![curr - Lo1] = s]
    /\ lo' = Lo1
    /\ file_content' = C1
    /\ diskPos' = D1
    /\ file_pointer' = D1
    /\ dirty' = TRUE
    /\ curr' = curr + 1
    /\ length' = Max(length, curr + 1)

WrittenCount(data) == Min(Len(data), Lo1 + BuffSz - curr)

WriteAtMost(data) ==
    LET k == WrittenCount(data)
        off == curr - Lo1
    IN
    /\ Len(data) > 0
    /\ curr + Len(data) <= MaxOffset
    /\ buff' = [i \in 0..(BuffSz-1) |->
                  IF off <= i /\ i < off + k THEN data[i - off] ELSE B1[i]]
    /\ lo' = Lo1
    /\ file_content' = C1
    /\ diskPos' = D1
    /\ file_pointer' = D1
    /\ dirty' = TRUE
    /\ curr' = curr + k
    /\ length' = Max(length, curr + k)

Next ==
    \/ FlushBuffer
    \/ \E p \in Offset : Seek(p)
    \/ \E n \in Offset : SetLength(n)
    \/ Read1
    \/ \E s \in Symbols : Write1(s)
    \/ \E n \in 1..MaxOffset : Read(n)
    \/ \E d \in WriteData : WriteAtMost(d)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)

Symmetry == Permutations(Symbols)

Alias == [dirty |-> dirty, length |-> length, curr |-> curr, lo |-> lo,
          buff |-> buff, diskPos |-> diskPos, file_content |-> file_content,
          file_pointer |-> file_pointer, logical |-> LogicalFileContent]

Inv2CanAlwaysBeRestored == ENABLED (Seek(curr) /\ Inv2')

Safety ==
    /\ AbsInit(LogicalFileContent, curr)
    /\ [][AbsNext(LogicalFileContent, curr)]_<<LogicalFileContent, curr>>

FlushBufferCorrect ==
    [][FlushBuffer => UNCHANGED <<LogicalFileContent, curr>>]_vars

SeekCorrect ==
    [][\A p \in Offset : Seek(p) => AbsSeek(LogicalFileContent, curr, p)]_vars

SeekEstablishesInv2 ==
    [][\A p \in Offset : Seek(p) => Inv2']_vars

Write1Correct ==
    [][\A s \in Symbols : Write1(s) => AbsWrite1(LogicalFileContent, curr, s)]_vars

Read1Correct ==
    [][Read1 => AbsRead1(LogicalFileContent, curr, B1[curr - Lo1])]_vars

WriteAtMostCorrect ==
    [][\A d \in WriteData :
         WriteAtMost(d) =>
            AbsWrite(LogicalFileContent, curr, Prefix(d, WrittenCount(d)))]_vars

ReadCorrect ==
    [][\A n \in 1..MaxOffset :
         Read(n) => AbsRead(LogicalFileContent, curr, ReadData(n))]_vars

=============================================================================
```