```tla
    /\ RAF_content = EmptyArray
    /\ RAF_pointer = 0
    /\ lastRead = EmptyArray

RAF_Seek(p) ==
    /\ RAF_pointer' = p
    /\ UNCHANGED <<RAF_content, lastRead>>

\* A read may return fewer than k symbols, but at least one if any remain
RAF_Read(k) ==
    \E n \in (IF RAF_pointer < Len(RAF_content)
                THEN 1..Min(k, Len(RAF_content) - RAF_pointer)
                ELSE {0}) :
        /\ lastRead' = Slice(RAF_content, RAF_pointer, n)
        /\ RAF_pointer' = RAF_pointer + n
        /\ UNCHANGED RAF_content

RAF_Write(c) ==
    /\ RAF_content' = WriteToFile(RAF_content, RAF_pointer, [i \in {0} |-> c])
    /\ RAF_pointer' = RAF_pointer + 1
    /\ UNCHANGED lastRead

\* Truncating moves the pointer back to the new end; extending does not
RAF_SetLength(n) ==
    /\ RAF_content' = Resize(RAF_content, n)
    /\ RAF_pointer' = IF Len(RAF_content) > n /\ RAF_pointer > n
                        THEN n ELSE RAF_pointer
    /\ UNCHANGED lastRead

RAF_Next ==
    \/ \E p \in Offset : RAF_Seek(p)
    \/ \E k \in 1..BuffSz : RAF_Read(k)
    \/ \E c \in Symbols : RAF_Write(c)
    \/ \E n \in Offset : RAF_SetLength(n)

RAF_Spec == RAF_Init /\ [][RAF_Next]_RAF_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete helpers.                                                       *)
(***************************************************************************)

\* Disk contents after flushing buffer b (logical length len) if drt holds
FlushDisk(drt, b, len) ==
    IF drt
        THEN WriteToFile(file_content, lo, Slice(b, 0, Min(hi, len) - lo))
        ELSE file_content

\* Buffer contents after loading from disk d at offset p
FillBuff(d, p) ==
    [i \in 0..(BuffSz - 1) |->
        IF p + i < Len(d) THEN d[p + i] ELSE ArbitrarySymbol]

\* OS file pointer after loading the buffer from disk d at offset p
FillPos(d, p) == p + Min(BuffSz, Max(0, Len(d) - p))

\* Install disk contents d and reload the buffer at offset p
ReloadAt(d, p) ==
    /\ file_content' = d
    /\ lo' = p
    /\ buff' = FillBuff(d, p)
    /\ diskPos' = FillPos(d, p)
    /\ dirty' = FALSE

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete operations.                                                    *)
(***************************************************************************)

Init ==
    /\ file_content = EmptyArray
    /\ dirty = FALSE
    /\ length = 0
    /\ curr = 0
    /\ lo = 0
    /\ buff = FillBuff(EmptyArray, 0)
    /\ diskPos = 0
    /\ lastRead = EmptyArray

\* Seeking inside the buffer only moves curr.
\* Otherwise, flush and reload the buffer at p.
Seek(p) ==
    /\ curr' = p
    /\ UNCHANGED <<length, lastRead>>
    /\ IF lo <= p /\ p < hi
          THEN UNCHANGED <<file_content, dirty, lo, buff, diskPos>>
          ELSE ReloadAt(FlushDisk(dirty, buff, length), p)

\* Read up to k symbols from the buffer.
\* If the buffer is exhausted, flush and refill it.
Read(k) ==
    LET avail   == Min(hi, length) - curr
        n       == IF avail > 0 THEN Min(k, avail) ELSE 0
        newCurr == curr + n
    IN  /\ lastRead' = Slice(buff, curr - lo, n)
        /\ curr' = newCurr
        /\ UNCHANGED length
        /\ IF newCurr < hi
              THEN UNCHANGED <<file_content, dirty, lo, buff, diskPos>>
              ELSE ReloadAt(FlushDisk(dirty, buff, length), newCurr)

\* Write one symbol at curr. Any gap past the old end of the file that falls
\* inside the buffer becomes ArbitrarySymbol.
Write(c) ==
    /\ curr < MaxOffset
    /\ LET newBuff == [i \in 0..(BuffSz - 1) |->
                         IF lo + i = curr THEN c
                         ELSE IF length <= lo + i /\ lo + i < curr
                                THEN ArbitrarySymbol
                                ELSE buff[i]]
           newLen  == Max(length, curr + 1)
           newCurr == curr + 1
       IN  /\ length' = newLen
           /\ curr' = newCurr
           /\ UNCHANGED lastRead
           /\ IF newCurr < hi
                 THEN /\ buff' = newBuff
                      /\ dirty' = TRUE
                      /\ UNCHANGED <<file_content, lo, diskPos>>
                 ELSE ReloadAt(FlushDisk(TRUE, newBuff, newLen), newCurr)

Flush ==
    /\ file_content' = FlushDisk(dirty, buff, length)
    /\ dirty' = FALSE
    /\ diskPos' = IF dirty THEN Min(hi, length) ELSE diskPos
    /\ UNCHANGED <<length, curr, lo, buff, lastRead>>

\* Flush, then truncate or extend the disk file, then reload the buffer
SetLength(n) ==
    LET d       == Resize(FlushDisk(dirty, buff, length), n)
        newCurr == IF length > n /\ curr > n THEN n ELSE curr
    IN  /\ length' = n
        /\ curr' = newCurr
        /\ UNCHANGED lastRead
        /\ ReloadAt(d, newCurr)

Next ==
    \/ \E p \in Offset : Seek(p)
    \/ \E k \in 1..BuffSz : Read(k)
    \/ \E c \in Symbols : Write(c)
    \/ Flush
    \/ \E n \in Offset : SetLength(n)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Internal invariants.                                                    *)
(***************************************************************************)

TypeOK ==
    /\ IsArrayOf(file_content, SymbolOrArbitrary)
    /\ dirty \in BOOLEAN
    /\ length \in Offset
    /\ curr \in Offset
    /\ lo \in Offset
    /\ buff \in [0..(BuffSz - 1) -> SymbolOrArbitrary]
    /\ diskPos \in Nat
    /\ IsArrayOf(lastRead, SymbolOrArbitrary)

BufferFixedSize == DOMAIN buff = 0..(BuffSz - 1)

CurrInBuffer == lo <= curr /\ curr < hi

DiskWithinLength == Len(file_content) <= length

\* A clean buffer agrees with the disk on every valid position
CleanBufferMatchesDisk ==
    ~dirty =>
        /\ Len(file_content) = length
        /\ \A i \in lo..(Min(hi, length) - 1) : buff[i - lo] = file_content[i]

DirtyImpliesWritten == dirty => lo < length

\* Unflushed extensions of the file must live in the buffer
ExtensionIsBuffered ==
    length > Len(file_content) => (dirty /\ length <= hi)

DiskPosConsistent == diskPos = FillPos(file_content, lo)

LogicalContentsOK ==
    /\ Len(LogicalFileContents) = length
    /\ IsArrayOf(LogicalFileContents, SymbolOrArbitrary)

Inv ==
    /\ TypeOK
    /\ BufferFixedSize
    /\ CurrInBuffer
    /\ DiskWithinLength
    /\ CleanBufferMatchesDisk
    /\ DirtyImpliesWritten
    /\ ExtensionIsBuffered
    /\ DiskPosConsistent
    /\ LogicalContentsOK

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement properties.                                                  *)
(***************************************************************************)

\* The whole behavior refines the abstract RandomAccessFile
Refinement == RAF_Spec

\* Each concrete operation refines its abstract counterpart
SeekRefinement ==
    [][\A p \in Offset : Seek(p) => RAF_Seek(p)]_vars

ReadRefinement ==
    [][\A k \in 1..BuffSz : Read(k) => RAF_Read(k)]_vars

WriteRefinement ==
    [][\A c \in Symbols : Write(c) => RAF_Write(c)]_vars

\* Flush has no abstract counterpart, so it must be an abstract stutter
FlushRefinement ==
    [][Flush => UNCHANGED RAF_vars]_vars

SetLengthRefinement ==
    [][\A n \in Offset : SetLength(n) => RAF_SetLength(n)]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking support.                                                 *)
(***************************************************************************)

Symmetry == Permutations(Symbols)

Alias ==
    [ file_content |-> file_content,
      dirty        |-> dirty,
      length       |-> length,
      curr         |-> curr,
      lo           |-> lo,
      buff         |-> buff,
      diskPos      |-> diskPos,
      lastRead     |-> lastRead,
      logical      |-> LogicalFileContents ]

(***************************************************************************)
(* TLC configuration (BufferedRandomAccessFile.cfg):                       *)
(*                                                                         *)
(*   CONSTANTS                                                             *)
(*       Symbols = {s1, s2}                                                *)
(*       ArbitrarySymbol = arb                                             *)
(*       MaxOffset = 3                                                     *)
(*       BuffSz = 2                                                        *)
(*   SPECIFICATION Spec                                                    *)
(*   SYMMETRY Symmetry                                                     *)
(*   ALIAS Alias                                                           *)
(*   INVARIANTS                                                            *)
(*       TypeOK                                                            *)
(*       BufferFixedSize                                                   *)
(*       CurrInBuffer                                                      *)
(*       DiskWithinLength                                                  *)
(*       CleanBufferMatchesDisk                                            *)
(*       DirtyImpliesWritten                                               *)
(*       ExtensionIsBuffered                                               *)
(*       DiskPosConsistent                                                 *)
(*       LogicalContentsOK                                                 *)
(*   PROPERTIES                                                            *)
(*       Refinement                                                        *)
(*       SeekRefinement                                                    *)
(*       ReadRefinement                                                    *)
(*       WriteRefinement                                                   *)
(*       FlushRefinement                                                   *)
(*       SetLengthRefinement                                               *)
(***************************************************************************)
=============================================================================
```