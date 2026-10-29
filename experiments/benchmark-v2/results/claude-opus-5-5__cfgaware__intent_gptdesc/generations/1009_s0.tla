```tla
  /\ length' = Max(length, curr + 1)
  /\ result' = <<>>

WriteAtMost(data) ==
  /\ data \in DataSeqs
  /\ curr < MaxOffset
  /\ LET l == WL(curr)
         b == WB(curr)
         k == Min(Len(data), Min(l + BuffSz - curr, MaxOffset - curr))
     IN /\ WindowUpd(curr)
        /\ buff' = [i \in BuffIdx |->
                      IF curr - l <= i /\ i < curr - l + k
                        THEN data[i - (curr - l) + 1]
                        ELSE b[i]]
        /\ dirty' = TRUE
        /\ curr' = curr + k
        /\ length' = Max(length, curr + k)
        /\ result' = <<>>

Next ==
  \/ \E p \in Offset : Seek(p)
  \/ \E n \in Offset : SetLength(n)
  \/ Read1
  \/ \E n \in 1..BuffSz : Read(n)
  \/ \E c \in Symbols : Write1(c)
  \/ \E d \in DataSeqs : WriteAtMost(d)
  \/ FlushBuffer

Spec == Init /\ [][Next]_vars

\* ------------------------------- Invariants ----------------------------------
TypeOK ==
  /\ file_content \in FileSeqs
  /\ file_pointer \in Nat
  /\ diskPos \in Nat
  /\ dirty \in BOOLEAN
  /\ length \in Offset
  /\ curr \in Offset
  /\ lo \in Offset
  /\ buff \in [BuffIdx -> SymOrArb]
  /\ result \in UNION {[1..n -> SymOrArb] : n \in 0..BuffSz}

\* Window is aligned and the pointer is in (or just past) the window
Inv1 ==
  /\ lo % BuffSz = 0
  /\ lo <= curr
  /\ curr <= lo + BuffSz

\* The pointer lies strictly inside the window (may be temporarily violated)
Inv2 == InWindow(curr)

\* Whenever Inv2 is broken, a dirty buffer can be flushed and a seek restores it
Inv2CanAlwaysBeRestored ==
  ~Inv2 => /\ (dirty => ENABLED FlushBuffer)
           /\ ENABLED Seek(curr)

\* Relationship between logical length and the underlying file
Inv3 ==
  /\ Len(file_content) <= length
  /\ (Len(file_content) < length) => (dirty /\ length <= lo + BuffSz)

\* Internal belief about underlying pointer matches the real one
Inv4 ==
  /\ diskPos = file_pointer
  /\ lo <= diskPos
  /\ diskPos <= lo + BuffSz

\* Buffer contents agree with the file
Inv5 ==
  /\ \A i \in BuffIdx : lo + i >= length => buff[i] = ArbitrarySymbol
  /\ ~dirty => \A i \in BuffIdx :
                  lo + i < length => buff[i] = FileAt(file_content, lo + i)

\* ------------------------ Per-operation refinement ---------------------------
FlushBufferCorrect ==
  [][FlushBuffer =>
       /\ LogicalFile' = LogicalFile
       /\ curr' = curr
       /\ file_content' = LogicalFile
       /\ ~dirty']_vars

SeekCorrect ==
  [][\A p \in Offset : Seek(p) =>
       /\ curr' = p
       /\ LogicalFile' = LogicalFile]_vars

SeekEstablishesInv2 ==
  [][\A p \in Offset : Seek(p) => Inv2']_vars

Write1Correct ==
  [][\A c \in Symbols : Write1(c) =>
       /\ LogicalFile' = AbsWriteF(LogicalFile, curr, <<c>>)
       /\ curr' = curr + 1]_vars

Read1Correct ==
  [][Read1 =>
       /\ LogicalFile' = LogicalFile
       /\ IF curr < length
            THEN result' = <<LogicalFile[curr + 1]>> /\ curr' = curr + 1
            ELSE result' = <<>> /\ curr' = curr]_vars

WriteAtMostCorrect ==
  [][\A d \in DataSeqs : WriteAtMost(d) =>
       \E k \in 1..Len(d) :
          /\ curr' = curr + k
          /\ LogicalFile' = AbsWriteF(LogicalFile, curr, SubSeq(d, 1, k))]_vars

ReadCorrect ==
  [][\A n \in 1..BuffSz : Read(n) =>
       /\ LogicalFile' = LogicalFile
       /\ Len(result') <= n
       /\ curr' = curr + Len(result')
       /\ result' = SubSeq(LogicalFile, curr + 1, curr + Len(result'))
       /\ (curr < length => Len(result') >= 1)]_vars

\* --------------------------------- Alias -------------------------------------
Alias ==
  [file_content |-> file_content,
   file_pointer |-> file_pointer,
   dirty        |-> dirty,
   length       |-> length,
   curr         |-> curr,
   lo           |-> lo,
   buff         |-> buff,
   diskPos      |-> diskPos,
   result       |-> result,
   logical      |-> LogicalFile]

=============================================================================
```